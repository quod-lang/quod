# Dictionnaires et ensembles (0.5) : note de conception

État : étapes 1 à 4 implémentées (2026-11-11). Étape 4 : `stdlib/maps.quod` a `get_or`, `count_up` et `merge`, prouvées ; `update` n'y est pas (il demanderait une fonction en paramètre), et `sum_values` a été écrite puis retirée, son contrat ne fixant pas le résultat. Écart de l'étape 3 : une énumération est une clé, mais `sorted` ne l'accepte pas (quel cas vient en premier serait un choix que personne n'a demandé) ; en C#, `sorted` ne couvre pas encore les structures. Écarts avec la proposition : `map_of` et `set_of` prennent une liste écrite sur place (une liste quelconque aurait demandé un pli dans les axiomes) ; les quantificateurs sur les éléments d'une séquence n'existaient pas, ils sont ajoutés pour les ensembles seulement ; le C# n'accepte pour l'instant que des clés entières, booléennes ou chaînes et des valeurs entières, booléennes, dictionnaires ou ensembles, et refuse une structure qui contient un dictionnaire ou un ensemble ; `sorted` est là, pour les chaînes et les booléens sans ordre connu du solveur ; les clés composées ne sont pas encore là. Le but : écrire une règle métier qui cherche une valeur par clé (un tarif, une catégorie, un droit) sans la coder dans une séquence de paires, dont la preuve est lourde et la lecture pénible. C'est le point que le README annonce avec les capacités ; il passe en premier, parce qu'il bloque plus tôt : l'hôte (Python ou C#) fait déjà les entrées-sorties.

## Ce que ça donne

```rust
fn price(tariffs: map<string, i64>, code: string) -> i64
  requires code in tariffs
  ensures result == tariffs[code]
{
  tariffs[code]
}

// un compte de mots : on construit un dictionnaire dans une boucle
fn count(words: seq<string>) -> map<string, nat>
  ensures forall w in keys(result): exists i in 0..len(words): words[i] == w
  ensures forall i in 0..len(words): words[i] in result
  ensures forall w in keys(result): result[w] == occurrences(words, w)
{
  let mut m: map<string, nat> = map_of([]);
  let mut i = 0;
  while i < len(words)
    invariant 0 <= i <= len(words)
    invariant forall j in 0..i: words[j] in m
    invariant forall w in keys(m): m[w] == occurrences(words[..i], w)
    decreases len(words) - i
  {
    let w = words[i];
    m = put(m, w, if w in m { m[w] + 1 } else { 1 });
    i = i + 1;
  }
  return m;
}
```

(`occurrences` est une fonction du programme, comme `sum` dans les exemples actuels.)

## Les décisions proposées

1. **Deux types, `map<K, V>` et `set<T>`, finis, immuables, à égalité structurelle.** Deux dictionnaires qui ont les mêmes clés et les mêmes valeurs sont égaux, quel que soit l'ordre dans lequel on les a construits. C'est ce que fait déjà `==` sur les séquences, les tuples et les types de données.
2. **Les clés sont d'un type ordonné.** `int`, `nat`, `i32`, `i64`, `char`, `bool`, `string` (ordre lexicographique), et les tuples, `struct` et `enum` faits de ces types (ordre lexicographique, cas dans l'ordre de déclaration). Pas de séquence ni de dictionnaire comme clé. Les valeurs, elles, sont de n'importe quel type.
   - **Pour :** un ordre total donne une représentation canonique (la même valeur, la même suite de clés), un moyen de parcourir sans exposer un ordre d'insertion ou de hachage qui varierait d'un backend à l'autre, et une traduction en C sans ramasse-miettes (un tableau trié de paires suffit à une première version).
   - **Contre :** un `set<seq<int>>` est refusé. Un tuple d'entiers fait l'affaire dans presque tous les cas d'usage d'une règle métier.
3. **Pas de nouvelle syntaxe, sauf l'indexation et `in`.** Les opérations sont des fonctions, comme `len` pour les séquences :
   - `map_of(pairs)`, `set_of(xs)` construisent depuis une séquence littérale (`map_of([])` est le dictionnaire vide ; le type vient du contexte, comme pour `[]`) ;
   - `m[k]` lit, avec l'obligation `k in m` comme `xs[i]` a l'obligation d'être dans les bornes ;
   - `k in m` et `x in s` sont des booléens (le mot `in` existe déjà dans `forall i in 0..n`) ;
   - `put(m, k, v)`, `remove(m, k)`, `add(s, x)`, `remove(s, x)` rendent une nouvelle valeur ;
   - `keys(m)` rend un `set<K>`, `len(m)` et `len(s)` rendent un `nat`, `union`, `inter`, `diff` et `subset` pour les ensembles.
   - **Ce qu'on écarte :** des littéraux `{k: v}`, qui se confondent avec les blocs `{ ... }` de l'analyseur, et des méthodes `m.put(...)`, que Quod n'a nulle part.
4. **`forall` et `exists` parcourent un ensemble ou `keys(m)`** (`forall w in keys(m): ...`). Les quantificateurs actuels ne parcourent que des intervalles `a..b` : celui-ci est nouveau, et ne vaut que pour les ensembles.
5. **Parcourir dans le code : par une séquence triée.** `sorted(s)` et `sorted_keys(m)` rendent une `seq` en ordre croissant sans doublon. On boucle avec un `while` sur cette séquence. Il n'y a pas d'itérateur ni d'ordre non spécifié : un résultat ne peut pas dépendre du backend.
6. **Une écriture `m = put(m, k, v)` dans une boucle ne recopie pas** quand le dictionnaire n'est pas partagé, comme l'ajout à une liste locale aujourd'hui (`appendable`). Sans cela, construire un dictionnaire de n entrées coûte n².
7. **Les bornes de type suivent les éléments.** Un `map<string, nat>` porte, comme une `seq<nat>`, le fait que toutes les valeurs sont `>= 0` ; un `set<i32>` que tous ses éléments tiennent dans `i32`.

## Ce qui reste tel quel

Un programme sans `map` ni `set` se compile et se prouve exactement comme avant : les programmes de référence, à l'octet près, comme pour les modules. `map`, `set`, `keys`, `put`... sont des noms de la bibliothèque, pas des mots réservés : une variable existante peut les garder en dehors de leur emploi.

## Dans le vérificateur

On suit ce que Quod fait pour les séquences : **un sort non interprété par instance** (`Map_<sig>`, `Set_<sig>`) et des fonctions non interprétées avec axiomes déclenchés, jamais la théorie des tableaux de Z3 (même raison que pour `Seq` : des preuves instables, une petite modification en corrigeant une et en cassant une autre).

- **Dictionnaire :** `m.has(m, k)`, `m.get(m, k)`, `m.size(m)`, `m.empty`, `m.put`, `m.remove`, `m.eq`. Axiomes de lecture : `has(put(m,k,v), k)`, `get(put(m,k,v), k) = v`, pour `k' != k` ils laissent `has` et `get` inchangés, `has(remove(m,k), k)` faux, `has(empty, k)` faux.
- **Égalité extensionnelle :** deux dictionnaires sont égaux si `has` et `get` coïncident partout, comme `Seq#Equal`.
- **Cardinal :** `size >= 0`, `size = 0 <=> m = empty`, `size(put(m,k,v)) = size(m) + (si has(m,k) alors 0 sinon 1)`, de même pour `remove`. C'est ce qui rend la finitude, et ce qui est le plus risqué pour la stabilité : il faut un jeu d'axiomes assez petit pour que les déclencheurs ne bouclent pas.
- **Ensemble :** même chose, sans `get`. `keys(m)` : `has(keys(m), k) <=> has(m, k)` et même cardinal. `union`, `inter`, `diff` par `has` ; leurs cardinaux ne sont encadrés que par des inégalités (`len(union(a,b)) <= len(a) + len(b)` et `>= max`), ce qui est sûr mais pas complet.
- **Vues triées :** `sorted(s)` a pour longueur `len(s)`, ses éléments sont strictement croissants, et `x in s` équivaut à l'existence d'un indice. Cet existentiel passe par une fonction de Skolem axiomatisée, à tester de près.
- **Faits de types :** `typeFacts` génère déjà le fait « tous les éléments d'une `seq<nat>` sont `>= 0` » ; il en faut l'analogue pour les valeurs et les clés bornées.
- **Contre-exemples :** pour une séquence, le modèle se lit par `len` et `nth`. Pour un dictionnaire il n'y a pas d'énumération des clés ; on lit `size`, puis `has`/`get` sur les clés qui apparaissent dans le modèle et dans le programme. À défaut, le contre-exemple dit « un dictionnaire à n entrées » sans les détailler. C'est un recul de lisibilité acceptable pour une première version.
- **Complétude :** la comparaison des deux résultats d'une fonction qui rend un `map` ou un `set` utilise `m.eq`, comme `Seq#eq`.
- **L'évaluateur :** `VMap` et `VSet` à clés triées, pour les contre-exemples par exécution et les entrées aléatoires (petits dictionnaires, clés tirées parmi les constantes du programme).

## Dans chaque backend

| Quod | Python | C# 7.3 | C (plus tard) |
|---|---|---|---|
| `map<K, V>` | `dict`, copié sauf non partagé | `Dictionary<K, V>` à l'intérieur, `IReadOnlyDictionary<K, V>` à la frontière | tableau trié de paires |
| `set<T>` | `frozenset` | `HashSet<T>` à l'intérieur, collection en lecture seule à la frontière | tableau trié |
| `sorted_keys(m)` | `sorted(m)` | tri explicite avec un comparateur ordonné | déjà trié |
| `m[k]` | `m[k]` | `m[k]`, avec l'exception d'une clé absente | recherche dichotomique |

- **Python :** un `str` Quod est déjà un `str` Python (avec les réserves connues de la 0.3). Les types de données sont des `dataclass` gelées, donc hachables. Les clés sont des scalaires, des `str` et des tuples : tous hachables.
- **C# :** `IReadOnlySet<T>` n'existe que depuis .NET 5 ; la cible .NET Framework 4.7.2 ne l'a pas. À la frontière, un ensemble en sortie est donc une `IReadOnlyCollection<T>` sans doublon, et en entrée une `IEnumerable<T>` qu'on copie dans un `HashSet`, comme on copie les listes d'entiers aujourd'hui. L'égalité structurelle des classes générées doit comparer des dictionnaires par contenu, ce que `Dictionary` ne fait pas : un comparateur à écrire.
- **Le C# public ne montre aucun `BigInteger`** (décidé en 0.4.0) : les clés et les valeurs entières sont des `long`, comme partout.

## Ce qu'on teste

- Analyse et typage : clé non ordonnée refusée avec un message qui nomme le type, mauvais nombre d'arguments, `m[k]` sans `k in m` refusé, `put` sur un type de valeur incompatible.
- Preuves : lecture après écriture, un dictionnaire construit dans une boucle (l'exemple du compte de mots), une propriété sur toutes les clés, `keys` et cardinal, ensemble et `union`. Un **corpus de temps** : chaque programme prouvé avant et après, comme on l'a fait pour les sorts non interprétés et pour `rlimit`, pour détecter une instabilité tôt.
- Trois exécutions comparées (évaluateur, Python, C#) sur un programme de règles réel, avec des cas aux bornes (clé absente, dictionnaire vide, `long.MinValue` comme clé).
- Mutants : les mutations de `put`, `remove`, `add`, `has` doivent être réfutées par les contrats d'un programme d'essai.
- Rien ne change pour un programme sans ces mots : les programmes de T6 à T11, à l'octet près.
- Un essai d'agent en fin de parcours, pas avant : « un agent écrit-il un programme de règles avec un dictionnaire à partir de la référence seule ? » Il se décide à part, avec une estimation de coût.

## Ordre de travail

1. **Types et opérations de base**, clés `int`, `char`, `bool`, `string`, vérification, évaluateur, Python et C#. C'est le gros du travail, et le seul qui touche les axiomes.
2. **Ensembles : algèbre et vues triées** (`union`, `inter`, `diff`, `subset`, `sorted`).
3. **Clés composées** : tuples, `struct`, `enum` d'éléments ordonnés.
4. **La bibliothèque standard** : `get_or`, `update`, `count`, écrits en Quod au-dessus des primitives.

## Questions ouvertes

1. **Clés d'un type ordonné seulement** (proposé), plutôt que tout type avec égalité ?
2. **Pas de nouvelle syntaxe que `m[k]` et `in`** (proposé), plutôt que des littéraux `{k: v}` ?
3. **Parcours par `sorted` / `sorted_keys` seulement** (proposé), plutôt qu'un `for` sur un ensemble ?
4. **`set<T>` et `map<K, V>` ensemble** (proposé), ou les ensembles d'abord ?
5. **Contre-exemples de dictionnaire dégradés** (nombre d'entrées plutôt que la liste) en première version : acceptable ?
6. **Frontière C# pour les ensembles** : une `IReadOnlyCollection<T>` sans doublon (proposé), ou rendre .NET 5 obligatoire pour les ensembles ?
