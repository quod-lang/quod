# Les entiers bornés : note de conception

État : proposition, rien n'est implémenté. Écrite sur Quod 0.1.5, pour la 0.3 ou après.

## Pourquoi

`int` est un entier mathématique, et le reste : c'est ce qui rend les preuves simples. Mais son coût est réel, avec un facteur 25 à 35
sur une boucle de somme en C#, et trois besoins le dépassent :

- **L'interopérabilité :** presque toute l'API .NET parle `int` et `long`. Une méthode qui rend un `BigInteger` oblige l'appelant à convertir.
- **Le code natif :** avec `BigInteger` partout, un backend C perd l'essentiel de son intérêt.
- **La vitesse :** les boucles de calcul, sans que la sémantique change.

Une option `--int long` est exclue : elle changerait le sens d'un programme déjà prouvé.

## Proposition

Deux types de plus, `i32` et `i64`. **Une opération dont le résultat sort des bornes n'est pas une erreur à l'exécution : c'est une
obligation de preuve non tenue.** Il n'y a ni débordement silencieux, ni exception en production, dans un programme vérifié.

```rust
fn midpoint(lo: i32, hi: i32) -> i32
  requires 0 <= lo <= hi
  ensures lo <= result <= hi
{
  lo + (hi - lo) / 2   // lo + hi aurait été refusé : la somme peut sortir de i32
}
```

| Question | Proposition | Raison |
|---|---|---|
| `int` reste-t-il le défaut ? | Oui | Un agent qui ne se soucie pas des bornes n'a pas de preuve de plus à écrire |
| Conversions vers le plus large | Implicites : `i32` vers `i64`, vers `int` | Toujours exactes |
| Conversions vers le plus étroit | Explicites, `to_i32(x)`, avec l'obligation que `x` tienne | Rien ne se tronque en silence |
| Littéraux | Typés par le contexte, avec l'obligation de tenir | `let x: i32 = 3000000000;` est une erreur |
| Dans les contrats et les invariants | **Calcul mathématique** | `ensures result == a + b` a son sens exact, sans débordement possible dans la spécification, comme en Dafny et en Verus |
| Dans le corps | Chaque `+`, `-`, `*`, `/`, `%` a son obligation de bornes | `i32.min / -1` déborde aussi |
| `/` et `%` | Euclidiens, comme `int` | Le C et le C# tronquent : le backend corrige pour un diviseur négatif, comme il le fait déjà |
| `len(xs)` | Reste un `nat`, avec un fait nouveau : `len(xs) <= 2^31 - 1` | Il permet `to_i32(len(xs))` et un indice en `i32` |
| Indices | Tout type entier | L'obligation d'être dans les bornes existe déjà |

**Le fait sur `len` est une nouvelle hypothèse du vérificateur.** Un `list` Python peut le dépasser en théorie : la fonction publique doit alors le refuser, sinon la preuve ne vaut plus.

## Dans le vérificateur

Le solveur raisonne déjà sur des entiers mathématiques : `i32` est un `Int` borné, avec des obligations de plus, et pas de bitvecteurs. C'est plus simple, et les preuves restent celles qu'on connaît. Le code exécuté doit alors ne jamais déborder, ce qui est exactement ce que les obligations garantissent.

L'**exécution avant le solveur** s'applique telle quelle : un débordement sur une petite entrée donne un contre-exemple certain, à condition d'ajouter les valeurs extrêmes (`i32.max`, `i32.min`) aux entrées essayées.

Le contrôle de **complétude** ne change pas : les résultats candidats doivent seulement respecter les bornes.

## Dans chaque backend

| Quod | Python | C# | C |
|---|---|---|---|
| `i32`, `i64` | `int` | `int`, `long` | `int32_t`, `int64_t` |
| `seq<i32>` | `list` | `IReadOnlyList<int>`, **sans vue ni copie** | tableau |
| Opérations prouvées | Sans contrôle | Sans `checked` | Sans contrôle |
| À la frontière publique | Vérifier les bornes : `int` Python n'en a pas | Le type le garantit | Le type le garantit |

En C, un débordement signé est un comportement indéfini. C'est le point où la preuve vaut le plus, et où une erreur du générateur coûte le plus : les tests devront passer sous les sanitizers, avec `--runtime-checks` qui garde des contrôles.

## Ce que ça coûtera aux agents

**C'est le risque principal.** Une somme sur une `seq<i32>` ne se prouve pas sans précondition sur les valeurs, ou sans un résultat plus large. Les invariants devront porter sur les bornes, et les contrats seront moins lisibles. Sur des tâches simples, nos modèles butent déjà sur les preuves.

Deux garde-fous : `int` reste le défaut, et le diagnostic d'un débordement doit dire quoi faire (élargir le résultat, ou ajouter un `requires` sur les valeurs), avec le contre-exemple. L'effet sur les agents sera à mesurer, et sur de nouvelles tâches, pas sur celles qui auront servi au réglage.

## Plus tard, sans changer le langage

Le backend pourra aussi **rétrécir lui-même** une variable locale `int` quand il prouve qu'elle reste dans `i32` : compteur de boucle, `lo`, `hi`, `mid`. La sémantique ne change pas, et la plupart des boucles gagnent en vitesse. Cela reste limité aux variables locales : faire dépendre une signature publique d'une preuve rendrait l'API instable.

## Décisions à prendre

1. **`i32` et `i64` seulement** dans un premier temps (proposé). `u8` viendra avec les octets et les fichiers, `u32` et `u64` au besoin.
2. **Le calcul mathématique dans les contrats** (proposé), comme Dafny et Verus.
3. **Le fait `len(xs) <= 2^31 - 1`** (proposé), avec son contrôle à la frontière.
4. **La place dans la feuille de route :** avec les chaînes en 0.3 (proposé, car les signatures publiques en dépendent) ou à part en 0.4.
