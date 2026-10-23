# Quod

*[English](README.md) · Français*

*Quod erat demonstrandum* : un langage de programmation conçu pour être **écrit par des agents IA**
et **vérifié par la machine**. Le programme arrive avec sa démonstration.

> **État : Quod 0.1, jeune mais réel.** Le compilateur vérifie les types, prouve les contrats avec
> Z3, contrôle que chaque contrat détermine son résultat, et compile vers Python. Un agent IA a
> écrit les six tâches VerifBench en Quod à partir de la seule référence du langage, et les six
> passent les tests cachés. Pas encore de version publiée : il se compile depuis les sources
> (voir plus bas).

## Thèse

Le goulot d'étranglement n'est plus l'écriture du code mais la **confiance** qu'on peut lui
accorder. Tout ce qui coûte cher à un humain (contrats exhaustifs, invariants, effets déclarés)
est quasi gratuit pour un agent. Quod exige donc ce que les humains refusent d'écrire, en échange
de code vérifié plutôt que simplement plausible.

Quod est indépendant de tout LLM : le juge est un solveur (SMT), le compilateur n'appelle jamais
de modèle, et un humain peut écrire du Quod, simplement plus laborieusement.

## Quod 0.1 en un programme

```rust
fn binary_search(xs: seq<int>, target: int) -> int
  requires forall i in 0..len(xs): forall j in i..len(xs): xs[i] <= xs[j]   // triée
  ensures -1 <= result < len(xs)
  ensures result >= 0 ==> xs[result] == target
  ensures result == -1 ==> forall i in 0..len(xs): xs[i] != target
  loose (r1, r2) => (r1 == -1) == (r2 == -1)   // n'importe quel indice d'un doublon convient
{
  let mut lo = 0;
  let mut hi = len(xs);
  while lo < hi
    invariant 0 <= lo <= hi <= len(xs)
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

```
$ quod check binary_search.quod
verified: 29 proof obligation(s) proved; 1 of 1 contract(s) determine their result; contracts: 1 by properties
```

Chaque indice, chaque invariant, la terminaison et les postconditions sont prouvés. Et le contrat
est **complet** : deux résultats différents ne peuvent pas le satisfaire tous les deux, sauf là où
`loose` déclare la liberté (les doublons). Un contrat qui en dit trop peu ne compile pas, et le
compilateur montre pourquoi :

```rust
fn clamp(x: int, lo: int, hi: int) -> int
  requires lo <= hi
  ensures lo <= result <= hi
{
  if x < lo { lo } else if x > hi { hi } else { x }
}
```

```
$ quod check clamp_weak.quod
clamp_weak.quod(4,1): error: in clamp: the contract accepts two different results for the same input: add ensures clauses until only the intended result is allowed, or declare the freedom with 'loose'
    witness: x = 0, lo = -1, hi = 0, result_a = 0, result_b = -1
rejected: 1 proof obligation(s) proved; 0 of 1 contract(s) determine their result, 1 underspecified; contracts: 1 by properties
```

Pour `x = 0` dans `[-1, 0]`, `0` (la bonne réponse) et `-1` satisfont tous deux le contrat : il lui
manque « `result == x` quand `x` est déjà dans l'intervalle ».

`quod build fichier.quod --target python` produit ensuite un module Python : les contrats prouvés
deviennent de la documentation, pas des vérifications à l'exécution.

## Contenu

| Dossier | Contenu |
|---|---|
| [src/Quod/](src/Quod/) | Le compilateur, en **F#**, livré comme binaire **Native AOT** (pas besoin de .NET pour l'utiliser) : analyse, typage, vérification (Z3 en SMT-LIB), contrôle de complétude, génération Python |
| [tests/](tests/) | Les tests du compilateur (xUnit), dont un test différentiel du Python généré contre l'évaluateur |
| [spec/](spec/) | Le langage : [Quod 0.1](spec/quod-0.1.fr.md) (ce qui existe), [brouillon du noyau](spec/kernel.fr.md) (où il va) |
| [examples/](examples/) | Des programmes qui se vérifient, et [des programmes qui doivent être rejetés](examples/bugs/) |
| [bench/](bench/README.fr.md) | **VerifBench** : la phase 0 (Python contre Dafny, écrits par des agents), et [les six tâches en Quod](bench/quod/README.fr.md), à la main et par un agent |
| [tools/dafny-complete/](tools/dafny-complete/) | La première brique, pour Dafny : un contrôle de spec complète qui trouve des témoins concrets des contrats sous-spécifiés |

## Compiler et essayer

Il faut le [SDK .NET 10](https://dotnet.microsoft.com/download) et la chaîne native qu'utilise
Native AOT (sous Windows, les outils C++ de Visual Studio) pour compiler, et
[Z3](https://github.com/Z3Prover/z3/releases) pour vérifier (sur le `PATH`, à côté de `quod`, ou
dans `QUOD_Z3`).

```bash
dotnet publish src/Quod -c Release -r win-x64 -o artifacts/aot
```

Avec `linux-x64` ou `osx-arm64` pour un autre système. Puis :

```bash
artifacts/aot/quod check examples/binary_search.quod
```

## Ce qu'on a appris jusqu'ici

*La phase 0 en détail (en anglais) : [Green proofs, empty promises: when AI agents write their own specifications](https://dev.to/malek_aitouaret_f026758c/green-proofs-empty-promises-when-ai-agents-write-their-own-specifications-59lf) (dev.to).*

- **Phase 0, Dafny.** Sommé d'écrire du Dafny *vérifié*, un modèle plus petit a produit des
  contrats qui se prouvent mais ne disent presque rien : 5 sur 8 ne contraignaient qu'une longueur,
  un format ou une forme. L'une de ces méthodes était fausse, et la preuve ne l'a pas vu. D'où le
  [pilier 5](spec/kernel.fr.md#5-spécifications-complètes) de Quod : chaque contrat doit déterminer
  son résultat.
- **Quod 0.1, par un agent.** Avec pour seul document la
  [référence du langage](spec/quod-0.1.fr.md#le-langage), un agent a écrit les six tâches VerifBench
  sans chaînes de caractères ; les six se vérifient et passent les tests cachés
  ([passage quod1](bench/quod/README.fr.md#un-agent-les-écrit)). Aucun contrat faible n'est passé.
- **Mais un contrat complet peut encore dire comment plutôt que quoi.** Quatre des six définissaient
  le résultat par une seconde implémentation, ou recopiaient le corps. `quod check` signale
  désormais le [style de chaque contrat](spec/quod-0.1.fr.md#style-des-contrats) (propriétés,
  modèle, recopie, aucun), avec un avertissement pour les deux derniers.
- **Un agent plus petit trouve les trous.** Un passage avec Haiku a trouvé trois manières de
  contourner le contrôle de complétude (un contrat qu'aucun modèle du solveur ne réfutait, un
  `loose` qui accepte tout, pas d'ensures du tout), toutes désormais détectées.

## Feuille de route

0. **Mesurer** (fait) : la vérification réduit-elle les bugs échappés, à quel coût ? Premier
   outil livré : [dafny-complete](tools/dafny-complete/).
1. **Quod 0.1** (presque terminé) : fonctions pures sur entiers, booléens, séquences et tuples,
   avec contrats, contrôle de complétude et génération Python. Reste : la finition des diagnostics
   JSON et des binaires Native AOT publiés pour Windows, Linux et macOS.
2. **Quod 0.2** : chaînes, types algébriques, modules, génériques, une construction `lemma`, un
   serveur MCP pour les agents.
3. **Quod 0.3** : capacités (aucune autorité ambiante : une fonction ne touche la console, les
   fichiers ou le réseau qu'au travers d'une capacité qu'elle reçoit), contrats scellés,
   dictionnaires et ensembles.
4. **Quod 0.4** : une génération C, vers le code natif et WASM.
5. **Quod 2.0 sera écrit en Quod.**

Le développement se fait en public. Si vous écrivez du Dafny, ou laissez des agents écrire du code
auquel vous devez faire confiance, issues et discussions sont les bienvenues.

## Licence

Quod est et restera **libre et gratuit**.

- Compilateur, outils et banc de mesure : **[Apache 2.0](LICENSE)**, permissive, avec une clause
  de brevets qui protège les utilisateurs.
- Spécification du langage ([spec/](spec/)) : **[CC BY 4.0](spec/LICENSE)** : chacun peut en
  écrire sa propre implémentation, en citant la source.

## Voisinage

- **Dafny, F\*, Lean, Verus** : langages à vérification intégrée ; Dafny est la référence de la
  phase 0, et l'encodage des séquences de Quod suit ses axiomes.
- **Qualité des spécifications écrites par des LLM** : le test symbolique de spécifications
  Dafny de Lahiri ([FMCAD 2024](https://arxiv.org/abs/2406.09757)) est l'ancêtre direct de la
  recherche de témoins ; voir aussi MutDafny, nl2postcond, Clover et le programme « intent
  formalization », résumés dans [docs/related-work.md](docs/related-work.md).
- **Unison** : code adressé par contenu.
- **[Warrant](https://github.com/mv2a/warrant)** : protocole de preuves pour du code écrit par des
  agents, agnostique du langage. Très proche dans l'intention ; Quod se place une couche en
  dessous (le langage lui-même) et pourrait en être un producteur de preuves.
