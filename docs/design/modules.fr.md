# Modules (0.3) : note de conception

Les modules passent avant les chaînes : la bibliothèque de chaînes sera écrite en Quod et prouvée ([chaines.fr.md](chaines.fr.md)). Le but est modeste : découper un programme en fichiers et réutiliser des fonctions prouvées. Rien de plus pour l'instant : ni paquets, ni versions, ni génériques.

## Ce que ça donne

```rust
// intervals.quod
private fn overlaps(a: (int, int), b: (int, int)) -> bool {
  a.0 <= b.1 && b.0 <= a.1
}

fn disjoint(a: (int, int), b: (int, int)) -> bool
  ensures result == !overlaps(a, b)
{
  !overlaps(a, b)
}
```

```rust
// planning.quod
import intervals

fn free_slot(a: (int, int), b: (int, int)) -> bool
  ensures result == intervals.disjoint(a, b)
{
  intervals.disjoint(a, b)
}
```

## Les décisions proposées

1. **Un fichier est un module, et son nom est celui du fichier.** Pas de déclaration `module`. Un nom de fichier doit être un identifiant Quod, sinon le fichier ne peut pas être importé.
2. **`import nom`, en tête de fichier, sans alias ni import partiel.** Un agent et un relecteur lisent tous deux `intervals.disjoint` et savent d'où ça vient. Un alias ou un `from x import y` ferait gagner quelques caractères et perdre cette lecture.
3. **Toujours le nom qualifié.** Une fonction importée s'appelle `intervals.disjoint`, même sans ambiguïté. Une fonction locale garde son nom court. Ajouter une fonction à un module ne peut donc casser aucun fichier qui l'importe.
4. **Tout est public, sauf `private fn`.** Les programmes existants restent valides. Une fonction privée ne s'appelle que depuis son module. Elle ne reçoit pas de contrôle aux frontières, et elle n'apparaît pas dans l'API générée.
5. **Résolution du nom :** d'abord à côté du fichier qui importe, puis dans la bibliothèque standard, embarquée dans le binaire. Un fichier local qui masque un module standard provoque un avertissement. Pas de variable d'environnement ni de chemin de recherche : la même commande donne le même résultat partout.
6. **Pas de cycle.** Un cycle d'imports est une erreur, qui nomme le cycle.

## Ce qu'une preuve voit

Exactement ce qu'elle voit aujourd'hui dans un même fichier :
- une fonction à corps d'expression est dépliée par sa définition, ce dont les contrats par modèle ont besoin ;
- une fonction à instructions n'est connue que par son contrat.

Un `ensures` public peut donc mentionner une fonction privée de son module, comme `overlaps` ci-dessus. Un appelant doit pouvoir lire ce que le contrat promet : `quod reference`, les diagnostics `review/model` et le code généré l'exposeront. Le masquer rendrait le contrat illisible, et donc invérifiable par un relecteur.

**Limite :** changer le corps d'un modèle importé peut casser une preuve dans un autre fichier. C'est voulu : cette preuve reposait dessus.

## Ce qui est vérifié, et quand

**`quod check planning.quod` vérifie le fichier et tout ce qu'il importe, à chaque fois.** Il n'y a pas de cache en 0.3 : un cache mal invalidé donnerait une preuve fausse, et un cache par empreinte peut attendre qu'un vrai programme en ait besoin. Une erreur dans un module importé est rapportée avec son propre fichier et sa ligne, et elle refuse la compilation. `--require-contracts` s'applique à tous les modules.

**La bibliothèque standard n'y fait pas exception**, contrairement à ce que prévoyait la première version de cette note. Elle se prouve en 1,4 s : la reprouver chez l'utilisateur coûte peu, et évite de lui faire confiance comme au compilateur. On pourra revoir ce choix si elle grossit.

## Le code généré

| Cible | Module Quod | Appel | Fonction privée |
|---|---|---|---|
| Python | `intervals.py` | `import intervals` puis `intervals.disjoint(...)` | `_overlaps` |
| C# | `public static class Intervals`, dans le même espace de noms, un `.cs` par module | `Intervals.Disjoint(...)` | `private static` |
| C (plus tard) | un `.c` et un `.h`, noms préfixés `intervals_` | `intervals_disjoint(...)` | `static` |

`quod build` écrit tous les modules du graphe. `Quod.Build` vérifie chaque fichier listé avec ce qu'il importe : un module partagé est donc prouvé plusieurs fois, ce qu'une passe unique pourra éviter si un vrai projet en souffre. Tout `.quod` voisin d'un fichier listé est une entrée de la compilation, pour qu'un module importé mais non listé ne laisse pas une preuve périmée. Rien ici n'exige de ramasse-miettes.

**Contrôles aux frontières :** un appel entre modules passe par la fonction publique, donc par ses contrôles, alors que la preuve les garantit déjà. Je garderais ces contrôles au début : ils coûtent peu et simplifient la génération. On pourra appeler directement l'implémentation si un banc montre que ça compte.

## Ce qui ne change pas

Un fichier sans `import` ni `private` se compile et se prouve exactement comme avant. Les programmes de T6 et T7 servent de test : mêmes diagnostics et même code généré, à l'octet près.

## Ce qu'on teste

- Tests de l'analyse : import inconnu, cycle, appel d'une fonction privée, nom non qualifié, masquage, nom de fichier invalide.
- Tests de preuve : un corps d'expression déplié entre modules, une fonction à instructions connue par son contrat seul, une erreur dans un module importé.
- Tests différentiels en Python et en C# sur un programme à trois modules.
- **Pas de nouvel essai d'agent :** il n'y a pas de question à mesurer. Les mutants à la version, comme d'habitude.

## Questions ouvertes

1. **`private` par mot-clé avec public par défaut** (proposé), ou `pub` obligatoire ? `pub` est plus sûr pour une API, mais casse tous les programmes existants et fait publier par défaut moins de contrats. Si un jour on veut changer, le faire avant la 1.0.
2. **Le serveur MCP :** `quod_check` reçoit soit un `path`, qui résout les imports à côté du fichier, soit un `source`, qui n'a pas de voisin. Je propose qu'avec `source`, un import ne puisse viser que la bibliothèque standard ou un fichier du répertoire du serveur, et que le message le dise.
