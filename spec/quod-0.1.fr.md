# Quod 0.1 : périmètre

*[English](quod-0.1.md) · Français*

> Statut : périmètre convenu (2026-10-22), avant l'implémentation. Le [brouillon du noyau](kernel.fr.md)
> décrit où va le langage ; ce document fixe ce que contient la première version, et rien de plus.

## Objectif

**Un agent écrit 6 des 8 tâches de base de VerifBench en Quod 0.1, à partir de la seule grammaire
donnée dans son prompt. Les programmes sont vérifiés, passent le contrôle de complétude, sont
compilés en Python et réussissent les mêmes tests cachés que les bras Python et Dafny.**

C'est le test « agent d'abord » : si un agent ne sait pas écrire du Quod à partir d'une grammaire
courte, le pari du langage doit être revu dès la 0.1, pas à la 1.0.

Les six tâches : `binary_search`, `merge_intervals`, `rle_encode`, `bounded_queue`,
`max_subarray`, `rotate` (les deux autres, `parse_int` et `balanced`, demandent des chaînes : 0.2).

## Choix techniques

- Compilateur écrit en **F#**, distribué en binaire **Native AOT** : aucun runtime .NET à installer.
- Solveur : **Z3**, interrogé en **SMT-LIB** via **un processus `z3` persistant** par compilation
  (`push` / `pop`). Voir le [prototype](../proto/z3-aot/README.md).
- Première cible : **Python**. C vient en second (0.4).
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

Un seul mot-clé, deux sortes de corps, distinguées par leur contenu :

- **Fonctions-expressions** : le corps est une seule expression (éventuellement
  `if c { a } else { b }`). Elles sont utilisables dans les contrats, et le vérificateur connaît
  leur définition.
- **Fonctions à instructions** : le corps contient des instructions. Elles ne sont appelables que
  depuis le code, et leurs appelants ne les connaissent que par leur contrat (vérification
  modulaire).

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
return e;              // ou une expression finale à la fin du corps
```

### Expressions

- Littéraux : entiers, `true`, `false`, `[a, b, c]`, `[]` (typé par le contexte), tuples `(a, b)`.
- Arithmétique : `+ - *`, et `/`, `%` avec preuve que le diviseur est non nul. **La division est
  euclidienne** (le reste est toujours `>= 0`), comme en SMT-LIB ; le backend Python émet une
  fonction d'aide, car le `//` de Python arrondit différemment pour les diviseurs négatifs.
- Comparaisons `== != < <= > >=`, logique `&& || !`, implications `==>` `<==>`.
- Séquences : `s[i]` (avec preuve que `0 <= i < len(s)`), `len(s)`, tranches `s[a..b]`,
  concaténation `s + t`.
- Appels d'autres fonctions (avec preuve de leurs `requires`).
- Dans les contrats et assertions : `result`, et des quantificateurs bornés
  `forall i in a..b: P`, `exists i in a..b: P` (`a` inclus, `b` exclu).

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
- `--runtime-checks` : au lieu d'échouer sur une obligation non prouvée, insérer un `assert` dans le
  Python généré, et le signaler dans le rapport (le statut ⚠️ du [principe 2](kernel.fr.md)).

## Complétude (pilier 5), intégrée

- Pour chaque fonction avec `ensures`, le compilateur demande à Z3 si deux résultats différents
  peuvent satisfaire le contrat pour une même entrée valide (ou si la relation `loose` déclarée est
  violée).
- `unsat` : ✅ déterminée. `sat` : ❌ sous-spécifiée, et **le modèle de Z3 est le témoin** (l'entrée et
  les deux résultats), sans avoir à exécuter la fonction. `unknown` : ⚠️ non conclu (un
  avertissement, pas une erreur).
- Une fonction sous-spécifiée ne compile pas, sauf liberté déclarée avec `loose`.

## Diagnostics

Lisibles par un humain par défaut, en JSON avec `--json`. Une entrée par constat :

```json
{
  "file": "search.quod", "fn": "binary_search", "line": 7, "col": 3,
  "kind": "proof | completeness | type | syntax",
  "status": "refuted | underspecified | inconclusive | error",
  "property": "invariant #2 preserved",
  "counterexample": { "xs": [0, 2], "target": 1 },
  "message": "..."
}
```

## Ligne de commande

```
quod check fichier.quod [--json] [--z3 CHEMIN] [--timeout SECONDES]
quod build fichier.quod --target python [-o DOSSIER] [--runtime-checks] [--json]
```

`z3` est cherché à côté de `quod`, puis dans `QUOD_Z3`, puis dans le `PATH`.

## Backend Python

- Un module Python par fichier Quod, une `def` par fonction, avec annotations de type.
- `seq<T>` devient une `list` Python (n'importe quelle séquence est acceptée en entrée), les tuples
  restent des tuples, `int`/`nat` deviennent `int`, `bool` reste `bool`.
- Les contrats prouvés ne produisent aucun code à l'exécution ; `--runtime-checks` ajoute des
  `assert` pour ceux qui ne le sont pas.

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
| 0.2 | chaînes et caractères, types algébriques (enums, `Option`), modules et imports, génériques, types raffinés généraux, un serveur MCP pour les agents |
| 0.3 | capacités et entrées-sorties, contrats scellés, tables associatives et ensembles |
| 0.4 | backend C |
| ... | ce qu'il faut à un compilateur, pour la 2.0 |

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
