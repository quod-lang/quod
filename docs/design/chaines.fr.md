# Les chaînes de caractères : note de conception

État : proposition, rien n'est implémenté. Écrite sur Quod 0.1.5, pour la 0.3.

## But

Les chaînes conditionnent le reste de la 0.3 : tout code métier en manipule, et le choix de `len(s)` et `s[i]`
engage tous les backends. Trois exigences :

- **La même réponse partout :** un programme prouvé rend le même résultat en Python, en C#, et plus tard en C.
- **Prouvable :** les preuves portent sur les chaînes comme sur les séquences, avec des outils déjà éprouvés.
- **Sans ramasse-miettes :** le type doit pouvoir se traduire en C (voir la feuille de route publique : backend C).

## Ce que `len(s)` compte

| Unité | `len("é")` en NFC | `len("😀")` | Indice en O(1) ? | Natif pour | Problème |
|---|---|---|---|---|---|
| Octet UTF-8 | 2 | 4 | oui | C, Rust | `s[i]` tombe au milieu d'un caractère ; un contrat sur « les caractères » devient faux |
| Unité UTF-16 | 1 | 2 | oui | C#, Java | Une moitié d'emoji est une « valeur » ; la sémantique de .NET s'imposerait à tout le langage |
| **Valeur scalaire Unicode** | 1 | 1 | selon la représentation | Python | L'indice n'est pas natif en C# et en C |
| Graphème | 1 | 1 | non | aucun | Dépend d'une table Unicode qui évolue : une preuve changerait de sens avec elle |

**Proposition : une chaîne est une suite immuable de valeurs scalaires Unicode.** C'est la seule unité qui ne coupe
jamais un caractère encodé et qui reste stable dans le temps. Le coût d'indexation à l'exécution est un problème de
représentation, traité plus bas, et non de sémantique.

**Ce que ça ne règle pas :** `"é"` en NFC et `"e" + accent` en NFD sont deux chaînes différentes, de longueurs 1 et 2.
Quod ne normalise rien en silence : ce serait changer les données. Une fonction de normalisation exigerait les tables
Unicode, donc une frontière de confiance. Pour des données d'OCR, c'est un vrai sujet : il faudra normaliser avant la frontière.

## Dans le langage

```rust
fn starts_with(s: string, p: string) -> bool
  ensures result == (len(p) <= len(s) && s[..len(p)] == p)
{
  ...
}
```

- **`string` est `seq<char>` pour le vérificateur.** Toutes les opérations sur les séquences (`len`, indice, tranche,
  concaténation, `==`, quantificateurs) existent déjà, et leur axiomatisation est éprouvée. C'est aussi la leçon des
  séquences : la théorie des chaînes de Z3 n'est pas utilisée, pour la même raison que sa théorie des séquences a été
  abandonnée (les faits quantifiés ne passaient pas).
- **`char` est un type à part**, pas un entier : `c >= 0` n'a pas de sens, et `'a' + 1` doit rester une erreur de type.
  `code(c)` et `char_of(n)` convertissent ; `char_of` a pour obligation que `n` soit une valeur scalaire
  (0 à 0x10FFFF, hors 0xD800 à 0xDFFF). Le vérificateur modélise `char` par un entier dans ces bornes.
- **Comparaison :** `==` et `<` portent sur les valeurs scalaires, sans culture ni locale. Une comparaison selon la langue n'est
  pas prouvable et dépend de la plateforme : elle reste du côté de l'appelant.
- **Bibliothèque écrite en Quod et prouvée :** `starts_with`, `ends_with`, `find`, `split`, `join`, `trim`, `parse_int`, `int_to_string`.
  Uniquement ASCII pour ce qui classe les caractères (`is_digit`), car la classification Unicode exige ses tables. Les deux tâches de
  base `parse_int` et `balanced` deviennent possibles.

## Dans chaque backend

| | Python | C# | C (plus tard) |
|---|---|---|---|
| **À la frontière publique** | `str` | `string` | UTF-8 validé et longueur |
| **En interne** | `str` | Sans surrogate : le `string` tel quel. Sinon : tableau de valeurs scalaires | Tableau de valeurs scalaires, à compteur de références ou en région |
| **`s[i]`** | O(1) | O(1) dans les deux cas | O(1) |
| **Coût à l'entrée** | Aucun | Un parcours O(n), une fois | Un parcours O(n), pour valider |
| **Entrée invalide** | Surrogate isolé refusé | Surrogate isolé refusé (`ArgumentException`) | UTF-8 invalide refusé |

**C'est le seul endroit où une garantie se paie à l'entrée :** le parcours en C# est nécessaire, parce qu'un surrogate isolé n'est pas une
valeur scalaire et contredirait le modèle prouvé. Le contrôle est linéaire, comme le coût de bien des appels sur des chaînes, et il reste à
mesurer sur de longs documents.

**Python :** `appendable` ne s'applique pas, `str` n'ayant pas d'ajout en place. Il faudra un tampon pour construire une chaîne dans une boucle, sinon le coût
est quadratique, comme le note l'optimisation des listes.

**Sans ramasse-miettes :** une chaîne est une valeur immuable sans cycle possible, donc le comptage de références ou les régions lui
conviennent. Le choix relève de la conception de la mémoire pour le C, pas de cette note.

## Validation

- Trois exécutions comparées (interpréteur, Python, C#), avec des entrées choisies pour ça : vide, ASCII, accents, NFD, emoji, surrogates isolés aux frontières.
- Les mutants sur la bibliothèque de chaînes.
- Les tâches de base `parse_int` et `balanced`, avec leurs tests cachés existants.

## Décisions à prendre

1. **La valeur scalaire comme unité de `len` et `s[i]`** (proposé).
2. **`char` comme type distinct de `int`** (proposé), plutôt qu'un entier raffiné, plus simple mais qui autoriserait l'arithmétique.
3. **Aucune normalisation, aucune locale dans le langage** (proposé) : c'est à l'appelant de normaliser avant la frontière.
4. **Une bibliothèque standard écrite en Quod dès la 0.3** (proposé) : elle demande les modules, qui sont aussi prévus en 0.3, et décide donc de l'ordre : modules, puis chaînes.
