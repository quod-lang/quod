# Types algébriques et génériques (0.3) : note de conception

État : implémenté, décisions approuvées. C'est le dernier morceau de la 0.3, après les modules, les chaînes et les entiers bornés. Le but : écrire une règle métier sans coder ses cas dans des entiers et des tuples.

## Ce que ça donne

```rust
// dans la bibliothèque standard : option.quod
enum Option<T> {
  None,
  Some(T),
}

// un programme
import strings
import option

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
    Accepted(c) => c == f.confidence && f.confidence >= threshold,
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

## Les décisions proposées

1. **`enum` avec données, `struct` avec des champs nommés.** Le `struct` n'était pas dans la feuille de route, mais une règle métier a besoin de `f.confidence` : `f.1` n'est lisible par personne. Il coûte peu une fois l'`enum` fait.
2. **`match` exhaustif, en expression.** Un cas oublié est une erreur de compilation qui le nomme. `_` est permis, et il est signalé comme à relire dans un `ensures`, car un nouveau cas y tomberait sans bruit.
3. **Pas de type récursif en 0.3.** Pas d'arbre ni de liste chaînée. Un type non récursif se copie par valeur, ce qui respecte l'exigence d'une traduction en C sans ramasse-miettes. Un arbre demanderait de choisir la gestion de la mémoire : ce choix mérite sa propre note, quand un besoin réel le justifiera.
4. **Les génériques par monomorphisation.** `first<T>` devient une copie par type utilisé, prouvée et générée pour ce type.
   - **Pour :** la preuve reste celle qu'on connaît, sur des types concrets, et le C n'aura besoin de rien de plus. Comme les modules, c'est réalisé avant le typage complet.
   - **Contre :** une fonction générique n'est prouvée que pour les types où elle sert. Une erreur porte sur une instance. Et le C# public ne peut pas exposer une méthode générique, seulement ses instances.
   - **Ce qu'on écarte :** prouver une fois pour tout `T`, avec un type opaque. C'est plus élégant, mais plus de travail dans le vérificateur, et sans bénéfice pour une première version.
5. **Types génériques et fonctions génériques seulement sur des types.** Ni contraintes (`T: Ord`), ni constantes. `==` sur `T` est permis, puisque tout type Quod a une égalité structurelle.
6. **Reporter les « types raffinés généraux » à la 0.4.** `requires` et `ensures` couvrent déjà le besoin, et la feuille de route les promettait surtout pour la lecture.

## Ce qui reste tel quel

Un programme sans `enum`, `struct`, `match` ni type générique se compile et se prouve exactement comme avant. `enum`, `struct` et `match` sont reconnus selon leur position, pour qu'une variable existante puisse garder ces noms.

## Dans le vérificateur

**Les `enum` et les `struct` deviennent des types de données de Z3**, comme les tuples aujourd'hui. Z3 connaît alors l'exclusivité des cas et leur injectivité sans axiome de notre part. `match` devient une cascade de tests et d'accès aux champs. La complétude et l'exécution avant le solveur s'étendent avec les petites valeurs de chaque type : un exemple de chaque cas.

## Dans chaque backend

| Quod | Python | C# 7.3 | C (plus tard) |
|---|---|---|---|
| `struct Field` | `dataclass(frozen=True)` | classe `sealed` immuable, égalité structurelle | `struct` par valeur |
| `enum Decision` | une `dataclass` par cas, plus un alias de type | classe `abstract` et classes `sealed` imbriquées, égalité structurelle | `struct` avec une étiquette et une `union` |
| `match` | cascade de `if` | cascade de `if` sur le type, sans `switch` d'expression (C# 8) | `switch` |
| `Option<int>` | `Option_int` et ses cas | la classe `Option_int` et ses cas | un `struct` par instance |

**Le C# :** une instance générique est une classe à part, `Option_int`, et non un générique C#, contrairement à ce que proposait la première version de cette note : c'est ce que donne la monomorphisation, et cela évite de traduire une seconde fois les règles de types. Le coût est une API moins lisible pour l'appelant, à juger sur du vrai code. Une classe publique a un constructeur qui contrôle ses champs.

## Ce qu'on teste

- Analyse : cas oublié, cas en double, nom inconnu, mauvais nombre d'arguments, type récursif refusé, champ inconnu.
- Preuves : une propriété par cas, un `match` dans un `ensures`, une `Option` dans une boucle.
- Trois exécutions comparées (interpréteur, Python, C#) sur un programme réel de règles.
- Rien ne change sans ces mots : les programmes de T6 et T7, à l'octet près.
- Pas d'essai d'agent : pas de question à mesurer.

## Questions ouvertes

1. **`struct` en plus de l'`enum`** (proposé) ?
2. **La monomorphisation** (proposé), plutôt qu'une preuve générique ?
3. **Pas de type récursif en 0.3** (proposé) ?
4. **Les types raffinés reportés à la 0.4** (proposé) ?
