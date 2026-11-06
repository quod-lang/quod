# Quod 0.1 : périmètre

*[English](quod-0.1.md) · Français*

> Statut : implémenté, et publié comme Quod 0.1 (2026-11-03). Le [brouillon du noyau](kernel.fr.md)
> décrit où va le langage ; ce document est ce que contient la première version, et rien de plus.
> `quod reference` affiche sa partie « langage » (en anglais).

## Objectif

**Un agent écrit 6 des 8 tâches de base de VerifBench en Quod 0.1, à partir de la seule grammaire
donnée dans son prompt. Les programmes sont vérifiés, passent le contrôle de complétude, sont
compilés en Python et réussissent les mêmes tests cachés que les bras Python et Dafny.**

C'est le test « agent d'abord » : si un agent ne sait pas écrire du Quod à partir d'une grammaire
courte, le pari du langage doit être revu dès la 0.1, pas à la 1.0.

Les six tâches : `binary_search`, `merge_intervals`, `rle_encode`, `bounded_queue`,
`max_subarray`, `rotate` (les deux autres, `parse_int` et `balanced`, demandent des chaînes : 0.3).

## Choix techniques

- Compilateur écrit en **F#**, distribué en binaire **Native AOT** : aucun runtime .NET à installer.
- Solveur : **Z3**, interrogé en **SMT-LIB** via **un processus `z3` persistant** par compilation
  (`push` / `pop`). Voir le [prototype](../proto/z3-aot/README.md).
- Première cible : **Python**. Ensuite **C#**, pour livrer des fonctions prouvées dans des bases de
  code .NET existantes (0.2). C, vers le code natif et WASM, vient plus tard.
- Le compilateur produit une représentation intermédiaire vérifiée ; chaque cible en est un
  traducteur.

## Le langage

### Types

| Type | Sens |
|---|---|
| `int` | entier mathématique, non borné (aucun débordement n'existe en 0.1) |
| `nat` | `int` dont on sait qu'il est `>= 0` ; seul type raffiné de la 0.1 |
| `bool` | `true`, `false` |
| `seq<T>` | séquence finie immuable |
| `(T1, T2, ...)` | tuple, composantes `t.0`, `t.1`, ... |

Affecter une expression `int` à un `nat` crée une obligation de preuve.

### Fonctions

```rust
fn nom(p1: T1, p2: T2) -> T
  requires P          // zéro ou plus
  ensures Q           // zéro ou plus ; `result` désigne la valeur renvoyée
  loose (r1, r2) => L // facultatif : liberté déclarée (pilier 5)
  decreases D         // obligatoire pour les fonctions récursives
{ corps }
```

Toutes les fonctions sont pures : pas d'entrée-sortie, pas de modification de leurs arguments.
Plusieurs résultats forment un tuple (`-> (int, int)`, `result.0`).

Deux sortes de corps, distinguées par leur contenu :

- **Fonctions-expressions** : le corps est une seule expression (éventuellement
  `if c { a } else { b }`). Elles sont utilisables dans les contrats, et le vérificateur connaît
  leur définition.
- **Fonctions à instructions** : le corps contient des instructions. Elles ne sont appelables que
  depuis le code, et leurs appelants ne les connaissent que par leur contrat (vérification
  modulaire).

Un **lemme** est une preuve, pas une fonction : il n'a pas de résultat, son `ensures` est ce qu'il
prouve, et son corps, les étapes de la preuve. Il se vérifie comme une fonction à instructions, et
il est **effacé** du code généré.

```rust
lemma nom(p1: T1, p2: T2)
  requires P          // zéro ou plus
  ensures Q           // ce qu'il prouve (pas de `result`)
  decreases D         // obligatoire pour les lemmes récursifs
{ étapes }            // assert, appels de lemmes, `if` pour séparer les cas ; pas de `return`
```

### Instructions

```rust
let x: T = e;          // liaison immuable (type facultatif s'il se déduit)
let mut y = e;         // variable locale mutable
y = e;                 // affectation d'une variable mutable
if c { ... } else { ... }
while c
  invariant I          // un ou plusieurs
  decreases D          // obligatoire
{ ... }
assert P;              // indication de preuve, vérifiée
nom_lemme(a, b);       // appel de lemme : une étape de preuve, effacée du code généré
return e;              // ou une expression finale à la fin du corps
```

### Expressions

- Littéraux : entiers, `true`, `false`, `[a, b, c]`, `[]` (typé par le contexte), tuples `(a, b)`.
- Arithmétique : `+ - *`, et `/`, `%` avec preuve que le diviseur est non nul. **La division est
  euclidienne** (le reste est toujours `>= 0`), comme en SMT-LIB ; le backend Python émet une
  fonction d'aide, car le `//` de Python arrondit différemment pour les diviseurs négatifs.
- Comparaisons `== != < <= > >=`, qui s'enchaînent (`0 <= i < n`), logique `&& || !`, implications
  `==>` `<==>`, conditionnelle `if c { a } else { b }` (une expression, `else if` permis).
- Séquences : `s[i]` (avec preuve que `0 <= i < len(s)`), `len(s)`, tranches `s[a..b]`, `s[a..]`,
  `s[..b]` (de `a` inclus à `b` exclu, avec preuve des bornes), concaténation `s + t`, égalité
  `s == t` (même longueur, mêmes éléments).
- Appels d'autres fonctions (avec preuve de leurs `requires`).
- Dans les contrats et assertions : `result`, et des quantificateurs bornés
  `forall i in a..b: P`, `exists i in a..b: P` (`a` inclus, `b` exclu).

### Structures, énumérations et génériques

Depuis la 0.3, un programme peut nommer ses données.

```rust
enum Decision {
  Accepted(int),
  Rejected(string),
  ToReview,
}

struct Field {
  name: string,
  confidence: i32,
}

fn decide(f: Field, threshold: i32) -> Decision
  ensures match result {
    Accepted(c) => c == f.confidence && c >= threshold && c >= 0,
    Rejected(_) => f.confidence < 0,
    ToReview => 0 <= f.confidence && f.confidence < threshold,
  }
{
  if f.confidence < 0 {
    Rejected("invalid: " + f.name)
  } else {
    if f.confidence >= threshold { Accepted(f.confidence) } else { ToReview }
  }
}
```

- Les champs d'un cas peuvent être nommés, `Accepted(value: int)`, pour qui les lit hors de Quod ; dans un `match`, ils se donnent dans l'ordre. Une valeur se construit comme un appel, dans l'ordre de ses champs : `Field("total", 80)`, `Accepted(3)`. Un cas sans champ est son nom : `ToReview`. Les champs d'un `struct` se lisent avec `f.name`, ceux d'un `enum` avec `match`.
- **`match` est une expression, et couvre tous les cas :** un cas oublié est une erreur de compilation qui le nomme. `_` couvre ceux qui ne sont pas nommés avant lui, et vient en dernier. Un nouveau cas y tombe alors sans bruit : dans un contrat, nommez-les plutôt.
- `==` compare par valeur. Un type ne peut pas se contenir : les types récursifs ne sont pas en 0.3.
- **Génériques :** `enum Option<T>`, `fn first<T>(xs: seq<T>) -> option.Option<T>`. Chaque usage fait une copie pour ses types, vérifiée et prouvée comme toute fonction : **une fonction générique n'est prouvée que pour les types où elle sert.** Les types viennent des arguments ou de ce qui est attendu ; si rien ne les dit, donnez son type à une variable. `T` n'a pas de contrainte.
- `import option` donne `Option<T>` (`None`, `Some`) et `Result<T, E>` (`Ok`, `Err`), `is_some`, `value_or`, `is_ok`.
- **Entre modules :** `fields.Candidate`, `fields.Candidate("a", 1)`, `option.None`. Dans un `match`, le type est connu, donc un cas s'écrit par son nom court : `Some(x)`.
- **En Python,** des `dataclass` figées, qui contrôlent ce que les types de leurs champs promettent à leur construction ; une copie de générique a ses propres noms, comme `Option__int_Some`.
- **En C#,** des classes immuables égales par valeur (`IEquatable<T>`, `==`, et un hachage sur ce qu'elles contiennent), qui copient les listes reçues et exposent des vues non convertibles. Un `enum` a une méthode `Match` avec une fonction par cas, qui donne à l'appelant l'exhaustivité de `match`. Imbriquées dans la classe du module : `Rules.Field`, et pour un `enum` une classe abstraite avec une classe `sealed` par cas : `Rules.Decision.Accepted`, dont les champs sont `Value`, ou `F0`, `F1` s'ils n'ont pas de nom. Deux soulignés de suite sont réservés au compilateur. Une copie de générique est une classe à part, `Option.Option_int`, et non un générique C#. Une fonction dont le nom serait celui d'un type reçoit `Of` : `level` à côté de `Level` donne `LevelOf`.

### Entiers bornés

Depuis la 0.3, `i32` et `i64` contiennent ce qui tient sur 32 et 64 bits. `int` reste le défaut : c'est un entier mathématique, et rien ne peut y déborder.

```rust
fn midpoint(lo: i32, hi: i32) -> i32
  requires 0 <= lo && lo <= hi
  ensures result == lo + (hi - lo) / 2
{
  lo + (hi - lo) / 2   // lo + hi serait refusé : la somme peut sortir de i32
}
```

- **Dans le code,** chaque `+ - * / %` et `-` unaire sur des opérandes bornés a une obligation : le résultat tient. Ce n'est ni un débordement silencieux ni une exception, mais une preuve non tenue, avec son contre-exemple.
- **Dans les contrats, les invariants et les assertions, le calcul est mathématique :** `ensures result == a + b` dit ce qu'il dit, sans débordement possible.
- **Ce qui élargit est implicite et exact :** `i32` vers `i64`, vers `int`. Ce qui rétrécit s'écrit, et doit être prouvé : `to_i32(x)`, `to_i64(x)`. Un littéral prend le type que son contexte attend, s'il tient.
- Sous une séquence ou un tuple, il n'y a pas de conversion : une `seq<i32>` n'est pas une `seq<int>`.
- Une opération entre un entier borné et un `int` ou un `nat` se fait en `int`. `len(xs)` reste un `nat`, sans borne : `to_i32(len(xs))` demande `requires len(xs) <= 2147483647`, contrôlé à la frontière publique.
- **Pour C#, préférez `i32` et `i64`.** Le `int` et le `nat` de Quod sont des entiers mathématiques, que C# ne peut tenir que dans un `BigInteger` : `int` en Quod n'est pas `int` en C#. `i32` est le `int` de C#, et `i64` son `long`.
- `/` et `%` sont euclidiens, comme pour `int`, dans tous les backends.
- En Python, un paramètre est contrôlé contre ses bornes à la frontière publique ; les éléments d'une liste seulement avec `--check-requires all`, ce que dit la docstring. En C#, ce sont des `int` et des `long`. Un `struct` ou un cas contrôle tout ce qu'il contient à sa construction, en profondeur.

### Caractères et chaînes

Depuis la 0.3, `char` est une valeur scalaire Unicode, et `string` est `seq<char>` : `len`, l'indice, les tranches, `+`, `==` et les quantificateurs s'y appliquent comme à toute séquence.

- Un littéral s'écrit `'a'` ou `"texte"`, avec les échappements `\n \t \r \0 \\ \' \" \u{1F600}`.
- `len(s)` compte les valeurs scalaires : un emoji vaut 1, une lettre avec un accent combinant vaut 2. Rien n'est normalisé et rien ne dépend d'une locale : normalisez avant la frontière.
- `char` n'est pas un entier. `'a' + 1` est une erreur de type. `code(c)` donne son numéro, et `char_of(n)` le caractère, avec l'obligation que `n` soit une valeur scalaire (0 à 10FFFF, hors D800 à DFFF). Deux `char` se comparent avec `<` par leurs valeurs scalaires.
- `import strings` donne la bibliothèque standard, écrite en Quod et prouvée avec votre programme : `is_digit`, `is_space`, `is_letter` (ASCII), `starts_with`, `ends_with`, `occurs_at`, `find`, `trim`, `split`, `join`, `all_digits`, `is_int`, `parse_int`, `int_to_string`. Un fichier local `strings.quod` la masque, avec un avertissement.
- En Python, une chaîne est un `str` et un `char` un `str` d'un caractère. En C#, une chaîne est un `string` et un `char` un `int`, sa valeur scalaire. Les deux refusent un surrogate isolé à la frontière.

- **Une longue entrée :** une fonction qui finit par s'appeler elle-même s'exécute en boucle, quelle que soit la longueur. Sinon, la profondeur d'une récursion suit son entrée. Pour ce cas, `run_by` : les contrats lisent une définition par récursion, et le code exécute une boucle prouvée égale. La boucle ne peut pas exiger plus que la fonction qu'elle exécute, ni la rappeler.

```rust
fn total(xs: seq<int>) -> int
  run_by total_loop
{
  total_upto(xs, len(xs))
}

fn total_loop(xs: seq<int>) -> int
  ensures result == total(xs)
{
  ...
}
```

### Modules

Depuis la 0.3, un fichier est un module, qui porte le nom du fichier. `import nom`, en tête de fichier, trouve `nom.quod` à côté de lui.

```rust
// planning.quod
import intervals

fn free_slot(a: (int, int), b: (int, int)) -> bool
  ensures result == intervals.disjoint(a, b)
{
  intervals.disjoint(a, b)
}
```

- Une fonction d'un autre module s'appelle toujours par son nom complet, `intervals.disjoint`. Une fonction du même module s'appelle par son nom court. Il n'y a ni alias ni import partiel.
- `private fn` ou `private lemma` ne s'appelle que depuis son module, et n'a pas de nom public dans le code généré. Tout le reste est public. Un `ensures` public peut mentionner une fonction privée de son module. **Rendez privée une fonction auxiliaire**, sauf si un autre module ou un appelant en a besoin : ce qui est public est l'API du code généré, et en C# une fonction auxiliaire sur `int` y montre un `BigInteger`.
- Une preuve voit une fonction importée comme une fonction locale : une fonction à corps d'expression par sa définition, une fonction à instructions par son contrat seul.
- `quod check` et `quod build` vérifient le fichier et tout ce qu'il importe, à chaque fois. Une erreur dans un module importé est rapportée dans ce fichier, et refuse le programme. Un cycle d'imports est une erreur.
- Dans le serveur MCP, un programme donné en `source` trouve ses imports dans le répertoire du serveur.

### Commentaires

`// ...` jusqu'à la fin de la ligne.

## Vérification

- Les conditions de vérification sont produites par plus faible précondition et envoyées à Z3 en
  SMT-LIB.
- Chaque obligation reçoit un statut : ✅ prouvée, ou ❌ réfutée **avec contre-exemple** ; un
  `unknown` ou un dépassement de délai du solveur est aussi une erreur.
- Obligations : `requires` de chaque appel, `ensures` à chaque retour, `invariant` de boucle (à
  l'entrée et préservé), `decreases` (boucles et récursion), bornes des séquences, diviseurs non
  nuls, affectations à un `nat`, `assert`.
- **Les obligations arithmétiques, à part.** Une obligation qui ne porte que sur des entiers et des
  booléens est aussi posée à un second processus z3, qui ne contient aucun axiome du programme
  (ceux des séquences sont quantifiés, et avec eux z3 n'emploie pas son solveur pour
  l'arithmétique non linéaire) : d'abord brièvement quand tous ses faits sont arithmétiques, et à
  nouveau quand le solveur partagé abandonne. Un bug comme `a == b * b * b` reçoit le même verdict,
  quoi que le fichier contienne d'autre.
- **Contre-exemples par exécution.** Avant de solliciter le solveur, le compilateur exécute chaque
  fonction sur de petites entrées qui satisfont son `requires` : les valeurs nulles, chaque
  constante entière du programme et ses voisines (`c - 1`, `c`, `c + 1`), puis des valeurs
  aléatoires (entiers dans -6..6 ou une constante, séquences de 0 à 5 éléments, ou aussi longues
  qu'une constante du programme, jusqu'à 50). Un paramètre que
  le `requires` définit à partir des autres, comme une table de sommes préfixes, est construit à
  partir d'eux. Quand peu d'entrées aléatoires satisfont le `requires` (un `requires` quantifié :
  quatre valeurs strictement croissantes à partir de 10), le solveur en trouve : pour chaque
  longueur de 0 à 6, une séquence est autant d'inconnues, les quantificateurs du `requires` se
  déplient sur l'intervalle connu, et la formule, sans quantificateurs, lui est facile ; des bornes
  aléatoires sur les inconnues varient les entrées, avec les cas limites d'un paramètre entier face aux
  éléments d'une séquence (égal à l'un d'eux, au-dessus de tous, en dessous de tous). Chaque obligation est vérifiée au passage, y compris que chaque appel récursif
  fait diminuer la mesure `decreases` (un appel qui ne la fait pas diminuer tournerait sans fin).
  Une obligation violée est signalée avec ces entrées : un contre-exemple confirmé, en quelques
  millisecondes. Quand le solveur échoue ensuite sur une obligation qu'aucune exécution n'a violée,
  le message donne les faits : combien d'exécutions, sur combien d'entrées essayées, qu'aucune ne
  l'a violée, et quelles branches de la fonction aucune exécution n'a prises
  (`no run took the 'if' at line 4 (condition true)`). Cela ne montre pas que la propriété est vraie (un bug peut demander d'autres
  entrées) ; si elle l'est, la preuve demande une indication. Quand aucune entrée essayée ne
  satisfait le `requires`, le message dit que la fonction n'a pas été exécutée.
- `--runtime-checks` : au lieu de refuser de compiler quand une obligation n'est pas prouvée,
  vérifier à l'exécution, dans le Python généré, les contrats des fonctions concernées, et les
  signaler dans le rapport (le statut ⚠️ du [principe 2](kernel.fr.md)).

### Indications et lemmes

Ce dont une preuve a besoin au-delà des contrats s'écrit dans le code, et se vérifie comme le reste :

- `assert P;` prouve P, puis le suppose. C'est la manière de nommer un fait que le solveur ne trouve
  pas seul, typiquement sur les tranches : `assert xs[..k + 1] == xs[..k] + [xs[k]];`.
- Un **lemme** énonce un fait dans son `ensures` et le prouve dans son corps. L'appeler, comme une
  instruction, donne le fait pour ses arguments : `sum_split(xs, i, j);`. Un lemme récursif est une
  preuve par récurrence : l'appel récursif est l'hypothèse de récurrence, et `decreases` la rend
  bien fondée.

  ```rust
  lemma sum_split(xs: seq<int>, i: nat, j: nat)
    requires i <= j <= len(xs)
    ensures sum(xs, 0, j) == sum(xs, 0, i) + sum(xs, i, j)
    decreases j - i
  {
    if i < j { sum_split(xs, i, j - 1); }
  }
  ```

  Les lemmes et leurs appels sont effacés du code généré : une preuve ne coûte rien à l'exécution.
  Un lemme n'a pas de valeur : il ne peut pas figurer dans une expression, et rien de ce qu'il
  prouve ne peut changer ce que le code calcule. Il n'est pas soumis au contrôle de complétude
  (il n'a pas de résultat à déterminer), et le résumé compte les lemmes à part.
- Un `exists` dans un invariant ou un `ensures` demande son témoin : garder, dans une variable,
  l'indice qui le rend vrai, et énoncer le fait pour cet indice ; le solveur n'invente pas de témoins.
- Les faits sur `a % n` pour un `n` que le solveur ne connaît pas dépassent le plus souvent Z3
  (arithmétique non linéaire) ; ceux où `a` est connu dans `0..2 * n` sont à sa portée.
## Complétude (pilier 5), intégrée

- Pour chaque fonction avec `ensures`, le compilateur demande à Z3 si deux résultats différents
  peuvent satisfaire le contrat pour une même entrée valide (ou si la relation `loose` déclarée est
  violée).
- `unsat` : ✅ déterminée. `sat` : ❌ sous-spécifiée, et **le modèle de Z3 est le témoin** (l'entrée et
  les deux résultats), sans avoir à exécuter la fonction. `unknown` : ⚠️ non conclu (un
  avertissement, pas une erreur).
- Une fonction sous-spécifiée ne compile pas, sauf liberté déclarée avec `loose`.
- Un `loose` qui déclare tout résultat acceptable est un **avertissement** (`loose-accepts-all`) :
  une relation vraie pour deux résultats quelconques (`loose (a, b) => true`), ou dont chaque
  partie ne concerne qu'un résultat (`a < len(xs) && b < len(xs)`, que l'ensures garantit déjà).
  Dans les deux cas, le contrôle de complétude ne prouve rien. Une relation dit ce que deux
  résultats acceptables ont en commun : `xs[a] == xs[b]` pour deux indices d'un maximum.
- Quand le résultat est un indice (`xs[result]`, `0..result`), les quantificateurs de l'`ensures`
  sont aussi donnés au solveur aux deux résultats : « le premier indice d'un maximum » est alors
  reconnu comme déterminé.

### Style des contrats

Un contrat déterminé peut encore dire peu : le plus court est `ensures result == <le corps>`, et les
agents l'écrivent. Chaque contrat est donc classé, dans le résumé de `quod check` et comme `note`
dans le JSON (`"kind": "contract"`) :

- **propriétés** (`properties`) : ce qu'est le résultat (bornes, ordre, appartenance...), pas
  comment le calculer ;
- **modèle** (`model`) : `result == f(...)`, avec `f` une fonction du programme (un modèle, ou une
  implémentation de référence) : la preuve montre que le code calcule ce que calcule le modèle,
  c'est donc le modèle que relit un relecteur ;
- **recopie** (`restated`) : `result == e` où `e` est, mot pour mot, une valeur que le corps
  renvoie. Un **avertissement** : la preuve ne montre alors guère plus que l'absence d'erreurs. Une
  petite formule qui est sa propre spécification peut rester telle quelle.
- **aucun** (`none`) : une fonction à instructions sans `ensures`. Un **avertissement** : rien n'est
  prouvé sur son résultat, et ses appelants, qui ne la connaissent que par son contrat, n'en savent
  rien. (Une fonction-expression sans `ensures` n'est pas classée : le vérificateur connaît sa
  définition.) Avec
  `--require-contracts` (`check`, `build`, `mcp`), c'est une **erreur**, tout comme une
  fonction-expression sans `ensures` qu'aucune autre fonction n'appelle , un `loose` qui accepte tout
  résultat, un lemme écrit comme une fonction, un `requires` qui fixe un paramètre à une valeur ou une séquence à une
  longueur de 0 ou 1, et un `requires` qui donne déjà l'`ensures` pour un argument renvoyé tel quel : `verified` signifie alors
  que quelque chose a été prouvé sur chaque résultat.
- **lemme écrit comme une fonction** (`lemma-as-function`) : une fonction à instructions qui
  renvoie un `bool`, `true` sur tous les chemins, ou qui dit `ensures result`, ses autres `ensures`
  étant des faits, et dont le programme n'utilise jamais la valeur (`if feature_enabled() { ... }`
  l'utilise ; un lemme ne le pourrait pas). Un **avertissement** : elle se vérifie, mais le code
  généré l'exécute à chaque appel. L'écrire comme un `lemma`, qui est effacé.

Les lemmes ne sont pas classés : leur `ensures` est ce qu'ils prouvent.

## Diagnostics

Lisibles par un humain par défaut, en JSON avec `--json`. Une entrée par constat :

```json
{
  "file": "sums.quod", "fn": "sum_to", "line": 7, "col": 3, "endLine": 7, "endCol": 30,
  "kind": "proof | completeness | type | syntax | contract | loose | review",
  "status": "refuted | underspecified | inconclusive | not-attempted | error | ...",
  "severity": "error | warning | note",
  "property": "invariant #2 is preserved by the loop body",
  "counterexample": { "n": "2" },
  "witness": { "x": "0", "result_a": "0", "result_b": "-1" },
  "evidence": "run | solver | unconfirmed",
  "reason": "timeout | incomplete quantifiers | ...",
  "message": "..."
}
```

- `counterexample` (une obligation de preuve) : les entrées qui la violent. `witness` (complétude) :
  l'entrée et les deux résultats différents que le contrat accepte.
- `evidence`, avec un contre-exemple : `run` (la fonction a été exécutée sur ces entrées et
  l'obligation a été violée : c'est certain), `unconfirmed`, `solver`. Un modèle trouvé par le
  solveur est exécuté lui aussi : si l'obligation est violée, l'`evidence` est `run` ; si
  l'exécution ne viole rien, le modèle est un état que le code n'atteint pas (typiquement un
  invariant trop faible pour prouver l'obligation), et le diagnostic est `inconclusive` et
  `unconfirmed` ; `solver` quand le modèle ne peut pas être exécuté. Un modèle candidat d'un
  `unknown` est lui aussi `unconfirmed`.
- `reason`, quand le solveur n'a pas conclu : `timeout`, ou ce qu'il en dit (`incomplete
  quantifiers`, `incomplete (theory arithmetic)`...). En mode texte, affichée après `solver:`.
- Des notes (`severity: note`, non affichées en mode texte) disent à un relecteur ce dont les
  preuves ne répondent pas : le style de chaque contrat (`contract`), chaque `loose` et sa relation
  (`loose`), et chaque fonction avec laquelle les contrats sont énoncés, directement ou à travers
  les fonctions-expressions qu'ils appellent (`review`, avec `property: "used by the contracts of
  f, g"`) : un contrat déterminé peut encore décrire la mauvaise fonction. La ligne de résumé les
  liste : `...; loose: binary_search; to review with the contracts: sum (prefix_sums, range_sum)`.

## Ligne de commande

```
quod check fichier.quod [--json] [--z3 CHEMIN] [--timeout SECONDES] [--budget SECONDES] [--require-contracts]
quod build fichier.quod [--target python|csharp] [--namespace NOM] [--check-requires all] [-o DOSSIER] [--runtime-checks] [--require-contracts] [--json]
quod mcp [--require-contracts]  # vérification, compilation, exécution et référence, servies à un agent IA (MCP, stdio)
quod reference [SECTION]   # la référence du langage, ou l'une de ses sections
quod contract fichier.quod cas.json --function NOM   # évalue un contrat sur des arguments et des résultats donnés
```

`z3` est cherché à côté de `quod`, puis dans `QUOD_Z3`, puis dans le `PATH`.

`--timeout` limite chaque essai du solveur sur une obligation de preuve (10 s par défaut ; une
obligation n'a droit à un second essai, sur un solveur neuf, que si le premier a abandonné vite,
pas après un dépassement de temps) ; `--budget` limite la
vérification entière (300 s par défaut, 0 pour aucune limite), car un agent l'attend en entier
avant de continuer. Les fonctions sont vérifiées dans l'ordre du fichier. Les obligations qui
restent quand le budget est épuisé ne sont pas envoyées au solveur : un diagnostic par fonction
dit combien, avec le statut `not-attempted` (et `reason: budget`), distinct d'un dépassement de
temps du solveur ; un contrôle de complétude laissé faute de temps est un avertissement de même
statut. Une preuve de terminaison laissée faute de temps n'est pas acquise : la définition de la
fonction reste inconnue du solveur.

## Backend Python

- Un module Python par fichier Quod. Chaque fonction est une `def nom` publique, qui met ses
  arguments en forme une fois, et une implémentation `_quod_f_nom`, qu'appelle le code Quod
  (récursion comprise), avec annotations de type. Les lemmes ne sont pas générés.
- `seq<T>` devient une `list` Python (n'importe quelle séquence est acceptée en entrée), les tuples
  restent des tuples, `int`/`nat` deviennent `int`, `bool` reste `bool`.
- `quod build` ne génère du code que pour un programme vérifié. Avec `--runtime-checks`, une
  fonction dont des preuves échouent est tout de même compilée, et ses contrats (requires, ensures,
  invariants avant chaque itération et après la dernière, assert) sont vérifiés à l'exécution, ainsi
  que ce qu'un type promet : le résultat `i32` ou `i64` d'une opération, le `nat` que devient un `int`,
  une conversion. Ils lèvent `AssertionError` ; ce ne sont pas des `assert` Python, donc `python -O`
  les conserve. Il en va de même des fonctions qui reposent sur une telle fonction, et de celles
  qu'elle appelle. Un contrat reconnu sous-spécifié bloque la compilation : aucune vérification à
  l'exécution ne peut dire qu'un résultat est celui voulu. Quand le solveur ne peut pas trancher,
  c'est un avertissement.
- Dans une telle fonction, l'indexation et les tranches vérifient leurs bornes (Python ferait boucler
  un indice négatif et tronquerait une tranche), et une division par zéro lève `ZeroDivisionError`.
  Un `nat` qui deviendrait négatif n'est pas vérifié.
- Les contrats prouvés ne produisent aucun code à l'exécution, seulement la docstring de la fonction.
- La sémantique de Quod là où Python diffère : `/` et `%` euclidiens (`_quod_div`, `_quod_mod`), et
  des séquences qui ne changent jamais. Une liste reçue en argument n'est pas copiée (le code
  généré ne modifie jamais un argument) : O(1) à l'entrée, et une recherche dichotomique reste en
  O(log n). Un tuple est converti en liste ; une séquence de tuples ou de séquences est reconstruite
  à la frontière publique (O(n)), car ses éléments peuvent arriver sous forme de listes. Une
  variable locale mutable étendue par `x = x + [e]` devient `x.append(e)` quand aucune autre
  variable, aucun argument, tuple ou séquence ne peut partager sa liste : une boucle qui construit
  une séquence reste en O(n), pas en O(n²). Les arguments n'étant pas copiés, une fonction qui
  renvoie un argument tel quel (`fn id(xs: seq<int>) -> seq<int> { xs }`) rend à l'appelant Python
  sa propre liste : la modifier ensuite modifie aussi son entrée, comme avec toute fonction Python.
  Les fonctions natives
  sont aliasées (`_quod_len`...), donc une fonction Quod nommée `len` ou `list` ne masque rien dont le
  code généré a besoin. Un nom qui est un mot-clé Python reçoit un `_` final.
- Limite connue : la récursion est celle de Python (profondeur 1000 par défaut).

Backend Python, depuis la 0.1.5 : **un appelant Python ne prouve rien.** Une fonction publique vérifie ses `requires`
sans quantificateur ni appel, et qu'un paramètre `nat` est `>= 0` (`ValueError`). Une liste de `nat` compte comme quantifiée. Les autres restent à la charge de l'appelant, et sa docstring le dit ;
`--check-requires all` les vérifie aussi, à leur coût. Chaque `loose` est montré avec deux résultats différents qu'il
accepte sur une entrée, dans le JSON et dans le résumé. Un modèle dont la définition se lit comme le corps, une fois
déplié, est classé `restated`.

## Backend C#

- Une classe par fichier Quod (`--namespace`, `Quod.Generated` par défaut), dans `Nom.g.cs`. Le code reste
  dans C# 7.3 et la bibliothèque standard, pour .NET Framework 4.7.2 comme pour .NET Core et suivants. Un
  projet .NET Framework référence `System.Numerics`.
- Chaque fonction donne une méthode publique en PascalCase et une implémentation privée `_quod_f_nom`, que le
  code Quod appelle. Les lemmes ne sont pas générés. Deux fonctions de même nom public sont refusées.
- `int` et `nat` sont `BigInteger`, `bool` est `bool`, `seq<T>` est `IReadOnlyList<T>` (sans copie à l'entrée),
  les tuples sont des `ValueTuple`. L'égalité est structurelle ; `/` et `%` sont euclidiens.
- **Un appelant C# ne prouve rien.** Une méthode publique vérifie `null` pour ses séquences, ses `requires`
  sans quantificateur ni appel, et qu'un paramètre `nat` est `>= 0` (`ArgumentException`). Une liste de `nat` compte comme quantifiée. Les autres restent à la charge de l'appelant, et son
  commentaire le dit ; `--check-requires all` les vérifie aussi, à leur coût. Les appels entre fonctions Quod ne
  vérifient rien.
- Une méthode avec une liste d'entiers a deux formes de plus, pour `int` et `long` : la liste est vue comme celle de
  Quod, sans copie. Le résultat reste un `BigInteger`. Définir `QUOD_CHECK_REQUIRES` dans le projet appelant vérifie
  aussi les `requires` quantifiés.
- Une fonction récursive appelle `EnsureSufficientExecutionStack` : une récursion trop profonde lève une
  exception au lieu de mettre fin au processus.
- Avec `--runtime-checks`, les contrats non prouvés et ce qu'un type promet lèvent `QuodContractException` (une opération sur `i32` ou `i64` est calculée sans borne, puis vérifiée), et les bornes d'une liste lèvent toujours.
- Le générateur n'est pas prouvé. Le code généré est testé contre l'évaluateur sur les programmes du dépôt, pour
  les deux cibles, et contre les tests cachés de VerifBench.

## Exemple

```rust
fn binary_search(xs: seq<int>, target: int) -> int
  requires forall i in 0..len(xs): forall j in i..len(xs): xs[i] <= xs[j]   // triée
  ensures -1 <= result && result < len(xs)
  ensures result >= 0 ==> xs[result] == target
  ensures result == -1 ==> forall i in 0..len(xs): xs[i] != target
  loose (r1, r2) => (r1 == -1) == (r2 == -1)   // n'importe quel indice d'un doublon convient
{
  let mut lo = 0;
  let mut hi = len(xs);
  while lo < hi
    invariant 0 <= lo && lo <= hi && hi <= len(xs)
    invariant forall i in 0..lo: xs[i] < target
    invariant forall i in hi..len(xs): xs[i] > target
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2;
    if xs[mid] < target { lo = mid + 1; }
    else if xs[mid] > target { hi = mid; }
    else { return mid; }
  }
  return -1;
}
```

## Hors de la 0.1

| Version | Contenu prévu |
|---|---|
| 0.2 | un backend C# (le serveur MCP est arrivé avec la 0.1.1) |
| 0.4 | types raffinés généraux |
| 0.4 | capacités et entrées-sorties, contrats scellés, tables associatives et ensembles |
| plus tard | backend C (code natif, WASM) ; ce qu'il faut à un compilateur, pour la 2.0 |

**Quod 2.0 sera écrit en Quod.** L'auto-hébergement demande des chaînes, des types algébriques (les
arbres syntaxiques), des tables associatives et des fichiers : ce sont les jalons entre la 0.1 et
la 2.0. D'ici là, le compilateur F# reste simple et nettement découpé en étapes, pour pouvoir être
réécrit.

## Étapes d'implémentation

1. Analyse syntaxique : arbre syntaxique F#, messages d'erreur avec position.
2. Vérification des types.
3. Conditions de vérification, session Z3 persistante.
4. Contrôle de complétude, témoins tirés des modèles de Z3.
5. Backend Python.
6. Les six tâches VerifBench en Quod : d'abord écrites à la main pour valider, puis par un agent à
   partir de la grammaire seule.
7. Diagnostics JSON, version Native AOT publiable (Windows, Linux, macOS).

## Terminé quand

1. Les six tâches, écrites à la main, sont vérifiées, passent le contrôle de complétude (ou
   déclarent `loose`), et réussissent les tests cachés de VerifBench une fois compilées en Python.
2. Un agent, qui ne reçoit que cette description du langage, les écrit ; les résultats sont
   présentés à côté des bras Python et Dafny de VerifBench.
3. `quod` tourne en binaire autonome sous Windows et Linux.
