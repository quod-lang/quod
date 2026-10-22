# Noyau de Quod — brouillon v0

*[English](kernel.md) · Français*

> Statut : notes de conception, pas encore une spécification normative. Les choix ci-dessous sont
> des hypothèses que la Phase 0 ([bench/](../bench/)) doit confirmer ou infirmer.

## Principes

1. **Syntaxe familière, sémantique nouvelle.** Surface proche de Rust/OCaml pour exploiter ce que
   les modèles savent déjà ; l'innovation est dans les contrats, les effets et la vérification.
   Grammaire assez courte pour tenir entière dans un prompt.
2. **Aucune propriété ignorée en silence.** Chaque propriété déclarée a un statut :
   - ✅ **prouvée** statiquement (SMT) ;
   - ⚠️ **vérifiée à l'exécution** — preuve échouée ou expirée : check inséré *et signalé* ;
   - ❌ **réfutée** — avec contre-exemple concret.
3. **Le compilateur parle aux machines.** Sa sortie principale est structurée (JSON), pas du texte.
4. **Pas de comportement indéfini, déterminisme par défaut.**
5. **Aucune autorité ambiante.** Tout accès au monde extérieur passe par une capacité reçue en
   paramètre (voir pilier 2).

## Les cinq piliers

### 1. Contrats obligatoires

Toute fonction publique porte `requires` / `ensures` ; toute boucle, `invariant` et `decreases`.

```rust
fn binary_search(xs: &[i64], target: i64) -> Option<usize>
  requires sorted(xs)
  ensures match result {
    Some(i) => i < len(xs) && xs[i] == target,
    None    => forall j in 0..len(xs): xs[j] != target,
  }
  loose (r1, r2) => r1.is_some() == r2.is_some()   // voir pilier 5
{
  let mut lo: usize = 0;
  let mut hi: usize = len(xs);
  while lo < hi
    invariant lo <= hi && hi <= len(xs)
    invariant forall j in 0..lo: xs[j] < target
    invariant forall j in hi..len(xs): xs[j] > target
    decreases hi - lo
  {
    let mid = lo + (hi - lo) / 2;
    if xs[mid] < target      { lo = mid + 1 }
    else if xs[mid] > target { hi = mid }
    else                     { return Some(mid) }
  }
  None
}
```

#### Contrats scellés

Quand l'agent écrit à la fois le code et son contrat, le chemin le plus court vers une
vérification verte peut être d'affaiblir le contrat. Et une fois la vérification verte, plus
personne ne lit le contrat : le vert agit comme un signal d'arrêt.

Un contrat peut donc être **scellé** : l'agent peut le lire, pas le modifier.

- Les contrats scellés sont enregistrés dans un fichier de verrouillage (`contracts.lock`), sous
  forme d'une empreinte par fonction. C'est un humain qui le met à jour avec `quod seal` ; les
  outils de l'agent (le serveur MCP) n'ont pas accès à cette commande et exposent les contrats
  scellés en lecture seule.
- Compiler une fonction dont le contrat scellé ne correspond plus au verrou est une erreur :

  ```json
  {
    "status": "error",
    "code": "sealed_contract_changed",
    "fn": "lru_cache",
    "change": "ensures #2 removed",
    "hint": "a sealed contract cannot be changed by the agent; propose a stronger one instead"
  }
  ```

- **Tout le chemin de vérification est scellé, pas seulement les contrats.** Si l'agent peut
  changer *ce qui est vérifié*, il peut contourner un contrat scellé en faisant pointer la
  vérification ailleurs. Quod n'a donc pas d'interrupteur de vérification : chaque fonction est
  toujours vérifiée (pas de `{:verify false}`, pas d'`assume`, pas d'axiome hors des fichiers
  scellés), et ce qui reste configurable (liste des modules, points d'entrée, limites du solveur)
  est lui aussi enregistré dans le verrou. Une différence est une erreur (`sealed_build_changed`),
  comme un contrat modifié.
- **Renforcer passe par des propositions.** L'agent peut proposer une version plus forte d'un
  contrat scellé dans un fichier de propositions, à côté des fichiers scellés mais en dehors. Pour
  chaque proposition, le compilateur prouve qu'il s'agit d'un raffinement (une précondition plus
  faible ou égale, `ancien requires ⇒ nouveau requires`, et une postcondition plus forte ou égale,
  `nouvel ensures ⇒ ancien ensures` sous l'ancienne précondition), et lui applique le contrôle de
  complétude du pilier 5. Un humain l'accepte ensuite avec `quod seal --accept`, ce qui garde les
  modifications du fichier scellé petites et délibérées. L'agent peut aider à resserrer un contrat
  trop lâche, jamais desserrer un contrat trop difficile.
- **Un contrat rédigé par un agent est sondé, pas seulement relu.** Une postcondition plausible qui
  ne contraint rien ressemble, à l'œil humain, à une postcondition solide. Avant qu'une proposition
  puisse être acceptée, son verdict de complétude et ses témoins (pilier 5) sont affichés à côté :
  la relecture s'appuie sur une sonde, pas seulement sur la lecture.
- **C'est le contrat que l'on relit.** Le rapport du compilateur liste, pour chaque fonction, le
  contrat et s'il a changé depuis le dernier scellement : la relecture porte sur le contrat, pas
  sur une coche verte.

*Crédit : ces règles viennent de pratiques décrites par [piekwerk](https://dev.to/piekwerk) dans
des commentaires sur l'article de la Phase 0
([le premier](https://dev.to/malek_aitouaret_f026758c/comment/3ieh0)) : des fichiers de spec et de
vérification placés hors de tout dossier où l'agent peut écrire ; un modèle de pull request qui
recopie le vrai bloc `requires` / `ensures` ; des invariants essentiels écrits à la main et gelés,
les contrats rédigés par l'agent passant par un fichier de propositions dont un humain reprend les
lignes ; la mise en garde selon laquelle la lecture seule doit couvrir tout le chemin de
vérification, point d'entrée et liste de fichiers compris ; et le constat que, sur un contrat
rédigé par un agent, une sonde par témoins vaut mieux qu'une relecture humaine. Prouver qu'une
proposition est un raffinement est notre extension.*

### 2. Effets par capacités

Quod n'a **aucune autorité ambiante** : pas de console, de fichiers, d'horloge ni de réseau
accessibles globalement. Pour agir sur le monde extérieur, une fonction doit **recevoir une
capacité** en paramètre. La signature dit donc à elle seule tout ce qu'une fonction *peut* faire.

```rust
fn load_config(fs: FsRead, path: Path) -> Config
  effects { fail(ParseError) }
```

`load_config` peut lire des fichiers — et rien d'autre : ni écrire, ni ouvrir le réseau, ni lire
l'heure. Un relecteur (humain ou agent) n'a pas besoin de lire le corps pour le savoir.

#### Règles

1. **Les capacités sont infalsifiables.** Aucun constructeur public : la seule source est le
   paramètre `sys: System` que le runtime passe à `main`. On ne peut pas en fabriquer, ni en
   ranger dans une constante ou un état global (il n'existe pas d'état global mutable).
2. **Elles se transmettent explicitement**, comme n'importe quelle valeur : `greet(sys.console)`.
   Une fonction n'a d'autorité que sur les capacités atteignables depuis ses paramètres.
3. **Elles s'atténuent, jamais ne s'amplifient.** On peut dériver une capacité plus restreinte,
   jamais l'inverse :

   ```rust
   let data: Fs     = sys.fs.subdir("data")   // confiné à ./data
   let ro:   FsRead = data.read_only()        // lecture seule
   ```

   Sous-typage : `Fs <: FsRead` — un `Fs` peut être passé là où un `FsRead` est attendu.
4. **Le déterminisme est structurel.** L'horloge (`Clock`) et l'aléa (`Rand`) sont aussi des
   capacités : une fonction qui n'en reçoit aucune est déterministe, par construction.
5. **La clause `effects` ne garde que les effets intrinsèques**, ceux qui ne passent pas par une
   capacité : `fail(E)` (erreur propagée), `alloc`, `diverge` (terminaison non prouvée). Omise,
   elle vaut `{}`. Une fonction sans paramètre-capacité et sans `effects` est **pure**.

#### Capacités du noyau

| Type | Autorité | Atténuations |
|---|---|---|
| `System` | racine, reçue par `main` uniquement | ses champs ci-dessous |
| `Console` | écrire sur stdout/stderr, lire stdin | `.stdout_only()` |
| `Fs` / `FsRead` | système de fichiers | `.subdir(p)`, `.read_only()` |
| `Clock` | heure courante | — |
| `Rand` | aléa | `.seeded(n)` (devient déterministe) |
| `Net` | réseau | `.only_host(h)` |
| `Env` | variables d'environnement, arguments | `.only(keys)` |

#### Des effets spécifiables

Chaque capacité expose un **modèle fantôme** (*ghost*), visible uniquement dans les contrats, qui
décrit son état observable. Pour `Console`, c'est `written: seq<str>`, tout ce qui a été écrit.
Les effets entrent ainsi dans le périmètre de la preuve :

```rust
fn greet(out: Console, name: str)
  requires len(name) > 0
  ensures out.written == old(out.written) + [greeting(name) + "\n"]
{
  out.write_line(greeting(name))
}
```

#### Tests sans mocks magiques

Comme l'autorité arrive par paramètre, un test passe simplement une capacité d'enregistrement :

```rust
test greet_writes_one_line {
  let c = Console.recorder()
  greet(c, "Ada")
  assert c.written == ["Hello, Ada!\n"]
}
```

#### Diagnostic

Utiliser une autorité qu'on n'a pas reçue est une erreur de compilation, avec un correctif proposé :

```json
{
  "status": "error",
  "code": "capability_missing",
  "location": { "fn": "greet", "line": 4 },
  "message": "`greet` writes to the console but receives no `Console` capability",
  "fix": { "add_parameter": "out: Console", "update_callers": ["main"] }
}
```

#### Pourquoi ce choix (plutôt qu'une simple clause `effects { console.write }`)

- **Moindre privilège** : `main` ne transmet à chaque fonction que ce dont elle a besoin, et
  l'atténuation (`subdir`, `read_only`) restreint encore plus finement qu'une liste d'effets.
- **Audit** : du code écrit par un agent ne peut pas « tricher » en atteignant une ressource
  globale ; tout chemin vers le monde extérieur est visible dans les signatures et dans `main`.
- **Testabilité** : on substitue des capacités, sans framework de mocks.
- **Prix** : des signatures plus longues et des capacités à faire circuler — exactement le genre de
  verbosité qui coûte cher à un humain et presque rien à un agent.

### 3. Types raffinés

```rust
type Percent = i32 where 0 <= _ && _ <= 100
type Index<xs> = usize where _ < len(xs)
```

Un accès `xs[i]` avec `i: Index<xs>` est prouvé : pas de bounds check à l'exécution.

### 4. Diagnostics pour agents

```json
{
  "status": "refuted",
  "property": "ensures #2 (None => forall j ...)",
  "location": { "fn": "binary_search", "line": 5 },
  "counterexample": { "xs": [1, 3, 5], "target": 3, "returned": "None" },
  "hint": "invariant #3 not preserved when xs[mid] > target"
}
```

Le contre-exemple est l'information la plus précieuse pour un agent : un cas concret à corriger
plutôt qu'une hypothèse à deviner.

### 5. Spécifications complètes

Un vérificateur ne garantit que ce qu'on lui demande. Une spécification trop faible est pire
qu'une absence de spécification : elle donne une **fausse confiance**.

**Constat de la Phase 0** (`bench/runs/hard1`) : sur `lru_cache`, Haiku a écrit en Dafny un code
faux, *entièrement prouvé*, parce que sa seule garantie était

```dafny
ensures |out| == CountGets(ops, |ops|)   // la longueur est juste… le contenu, libre
```

#### Le contrôle

Pour chaque fonction, en plus de prouver le corps, le vérificateur prouve que le contrat
**détermine le résultat de manière unique** :

```
∀ entrées vérifiant requires, ∀ r₁ r₂ :  ensures(r₁) ∧ ensures(r₂)  ⇒  r₁ == r₂
```

Le « résultat » inclut la valeur de retour **et** l'état fantôme des capacités après l'appel
(`out.written`, etc.) : un effet sous-spécifié est détecté comme une valeur sous-spécifiée.

Le contrôle ne regarde que le contrat, jamais le corps : c'est une question posée à la spec
elle-même — « autorise-t-elle plus d'une réponse ? ».

#### Statuts

- ✅ **déterminée** — l'unicité est prouvée ;
- ❌ **sous-spécifiée** — avec un **témoin** : une entrée et deux résultats distincts dont le
  contrat est *prouvé* sur chacun. Le verdict exige ce témoin : sans lui, pas de ❌ ;
- ⚠️ **non conclu** — ni preuve d'unicité, ni témoin : signalé, jamais ignoré (principe 2).

Une fonction sous-spécifiée **ne compile pas**, sauf liberté déclarée (ci-dessous). Une fonction
« non conclu » compile avec un avertissement ; l'agent peut ajouter un lemme d'unicité.

Pour trouver un témoin quand la preuve d'unicité échoue, le compilateur essaie de petites entrées
concrètes et des résultats voisins de la réponse produite par le code. Mesuré en Phase 0 sur les
24 solutions Dafny : les 6 vraies sous-spécifications ont toutes un témoin, les 3 fausses alertes
(formes canoniques dont l'unicité demande une induction) n'en ont aucun. Ce contrôle est
disponible dès aujourd'hui pour Dafny : [dafny-complete](../tools/dafny-complete/).

```json
{
  "status": "underspecified",
  "fn": "lru_cache",
  "witness": {
    "input": { "capacity": 1, "ops": [[0, 0, 0], [0, 0, 1]] },
    "result_a": [-1, -1],
    "result_b": [0, -1]
  },
  "hint": "ensures constrains only |out|; both results satisfy it"
}
```

Face à ce témoin, l'agent voit immédiatement ce qui manque : rien ne dit *quelle* valeur un `get`
doit renvoyer.

#### Liberté déclarée : `loose`

Certaines fonctions ont légitimement plusieurs réponses correctes. On le **déclare**, en disant
précisément ce qui peut varier, sous forme d'une relation entre deux résultats acceptables :

```rust
fn binary_search(xs: &[i64], target: i64) -> Option<usize>
  requires sorted(xs)
  ensures match result {
    Some(i) => i < len(xs) && xs[i] == target,
    None    => forall j in 0..len(xs): xs[j] != target,
  }
  // Avec des doublons, n'importe quel indice de `target` convient ;
  // mais trouvé / pas trouvé, lui, est déterminé.
  loose (r1, r2) => r1.is_some() == r2.is_some()
```

Le contrôle prouve alors `ensures(r₁) ∧ ensures(r₂) ⇒ loose(r₁, r₂)` au lieu de `r₁ == r₂`. Sans
clause `loose`, la relation par défaut est l'égalité. La liberté devient ainsi **une décision
visible et vérifiée**, et non un oubli.

#### Ce que le contrôle ne garantit pas

- **Complète ne veut pas dire juste.** Une spec peut déterminer un résultat unique… et faux. Le
  contrôle élimine les specs trop *faibles*, pas les specs *erronées* : l'adéquation à
  l'intention reste à valider (relecture, exemples, tests de propriétés).
- **Le piège du second programme.** Une spec du type `ensures out == Model(ops)`, où `Model` est
  une réimplémentation fonctionnelle, passe toujours le contrôle — et peut porter le même bug que
  le code. Le diagnostic signale ce style (*spec par modèle*) pour inciter à des propriétés
  déclaratives (quantificateurs, invariants) quand c'est possible. Observé en Phase 0 sur
  `bounded_queue`.
- **Coût** : une requête SMT de plus par fonction, souvent plus difficile que la preuve du corps
  (deux résultats symboliques).

## Questions ouvertes

- **Spécifications complètes (pilier 5)** : mesuré sur les 24 solutions Dafny de la Phase 0
  (voir [dafny-complete](../tools/dafny-complete/)) : l'unicité est prouvée sans aide pour 15,
  et les 3 échecs sur des specs complètes sont des formes canoniques. Restent à mesurer sur du
  code réel : la part de fonctions qui ont besoin de `loose`, et le passage à l'échelle sur des
  structures riches (cartes, ensembles, tas).
- **Contrats scellés** : où vivent-ils (à côté du code, ou dans des fichiers de spec séparés) ?
  Peut-on sceller un module entier ? Quelle interaction avec `loose` (élargir une relation `loose`
  est-il un affaiblissement) ?
- **Décidabilité / temps de preuve** : quel fragment logique garantir pour éviter les timeouts SMT ?
- **Capacités et concurrence** : comment partager une capacité entre tâches parallèles
  (copie, emprunt, linéarité) sans perdre la précision du modèle fantôme ?
- **Code adressé par contenu** (façon Unison) : dès le noyau, ou plus tard ?
- **Éditions sur AST** plutôt que sur texte : quelle interface exposer aux agents ?
- **Articulation avec Warrant** : Quod comme producteur de preuves pour ce protocole ?
