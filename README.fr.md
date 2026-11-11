# Quod

*[English](README.md) · Français*

*Quod erat demonstrandum* : un langage de programmation conçu pour être **écrit par des agents IA**
et **vérifié par la machine**. Le programme arrive avec sa démonstration.

> **État : Quod 0.4, une expérience qui fonctionne et qui est jeune.** Le compilateur vérifie les
> types, prouve les contrats avec Z3, contrôle que chaque contrat détermine son résultat, et compile
> vers Python et vers C#. Il n'a que des fonctions pures : pas d'entrées-sorties, pas encore de
> dictionnaires ni d'ensembles. Des agents y ont écrit des programmes de 300 lignes à partir de la
> seule référence. Ce qui a été mesuré, surtout négatif, est
> [plus bas](#ce-quon-a-appris-jusquici). Il a peu servi hors de son auteur : **les retours et les
> rapports de bogues sont ce dont il a le plus besoin.** [Le télécharger](https://github.com/quod-lang/quod/releases/latest) : z3 est inclus.

## Thèse

Le goulot d'étranglement n'est plus l'écriture du code mais la **confiance** qu'on peut lui
accorder. Tout ce qui coûte cher à un humain (contrats exhaustifs, invariants, effets déclarés)
est quasi gratuit pour un agent. Quod exige donc ce que les humains refusent d'écrire, en échange
de code vérifié plutôt que simplement plausible.

Quod est indépendant de tout LLM : le juge est un solveur (SMT), le compilateur n'appelle jamais
de modèle, et un humain peut écrire du Quod, simplement plus laborieusement.

## Quod en un programme

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
verified: 29 proof obligation(s) proved; 1 of 1 contract(s) determine their result; contracts: 1 by properties; loose: binary_search
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
`--target csharp` produit du C# 7.3 (donc .NET Framework 4.7.2 comme .NET) : le `int` de Quod est un `long`
calculé en `checked`, et un dépassement lève une exception au lieu de rendre un résultat faux (`i32` et
`i64` ont leurs bornes prouvées).

## Ce que Quod ne sait pas faire encore

- **Pas d'entrées-sorties, pas de fichiers, pas de réseau.** Une fonction Quod est pure : elle calcule un résultat à partir de ses arguments. On l'appelle depuis Python ou C#.
- **Pas de dictionnaires ni d'ensembles**, pas de classes ni d'héritage (structures, énumérations, `match` et génériques existent).
- **La vérification peut refuser un programme correct** (le solveur abandonne sur certaines arithmétiques non linéaires ou quantificateurs profonds), et elle prend de quelques secondes à une minute sur des programmes de quelques centaines de lignes.
- **Plateformes :** développé et testé sous Windows. Les binaires Linux et macOS sont construits et testés par la CI, mais très peu lancés à la main. Dites-nous si l'un ne marche pas.

## Contenu

| Dossier | Contenu |
|---|---|
| [src/Quod/](src/Quod/) | Le compilateur, en **F#**, livré comme binaire **Native AOT** (pas besoin de .NET pour l'utiliser) : analyse, typage, vérification (Z3 en SMT-LIB), contrôle de complétude, génération Python et C#, serveur MCP |
| [tests/](tests/) | Les tests du compilateur (xUnit), dont un test différentiel du Python généré contre l'évaluateur |
| [spec/](spec/) | Le langage : [référence](spec/quod-0.1.fr.md) (ce qui existe, tenue à jour bien que le nom du fichier dise 0.1), [brouillon du noyau](spec/kernel.fr.md) (où il va) |
| [examples/](examples/) | Des programmes qui se vérifient, et [des programmes qui doivent être rejetés](examples/bugs/) |
| [bench/](bench/README.fr.md) | **VerifBench** : la phase 0 (Python contre Dafny, écrits par des agents), et [les six tâches en Quod](bench/quod/README.fr.md), à la main et par un agent |
| [tools/dafny-complete/](tools/dafny-complete/) | La première brique, pour Dafny : un contrôle de spec complète qui trouve des témoins concrets des contrats sous-spécifiés |

## Installer et essayer

[Télécharger le paquet de votre système](https://github.com/quod-lang/quod/releases/latest) (Windows x64, Linux x64, macOS
sur puce Apple), le décompresser, et lancer `quod` depuis ce dossier : z3 est à côté, rien d'autre
à installer. Sous macOS, les binaires ne sont pas signés : lancer d'abord
`xattr -d com.apple.quarantine quod z3` dans le dossier.

```bash
quod check examples/binary_search.quod
quod build examples/prefix_sums.quod --target python
```

Depuis un agent IA, sans shell : `quod mcp` est un serveur MCP, voir [docs/mcp.fr.md](docs/mcp.fr.md)
(une ligne pour Claude Code, et une section à copier dans AGENTS.md).

Pour compiler depuis les sources, il faut le [SDK .NET 10](https://dotnet.microsoft.com/download)
et la chaîne native qu'utilise Native AOT (sous Windows, les outils C++ de Visual Studio), et
[Z3](https://github.com/Z3Prover/z3/releases) pour vérifier (sur le `PATH`, à côté de `quod`, ou
dans `QUOD_Z3` ; les versions publiées utilisent la 4.12.1, aussi sur PyPI sous le nom
`z3-solver`).

```bash
dotnet publish src/Quod -c Release -r win-x64 -o artifacts/aot
```

Avec `linux-x64` ou `osx-arm64` pour un autre système. Puis :

```bash
artifacts/aot/quod check examples/binary_search.quod
```

Sans accès à NuGet (hors ligne, ou derrière un réseau restreint), Native AOT est hors de portée :
il lui faut le paquet ILCompiler. Compiler alors un programme .NET ordinaire, qui ne demande aucun
paquet à télécharger (FSharp.Core est livré avec le SDK, dans `sdk/<version>/FSharp/library-packs`),
et le lancer avec le runtime .NET 10 :

```bash
dotnet build src/Quod -c Release -p:PublishAot=false
dotnet src/Quod/bin/Release/net10.0/quod.dll check examples/binary_search.quod
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
- **Depuis, des résultats surtout négatifs ou modestes.** Sur 72 passages à tâches inédites (quatre
  bras, six tâches), la mesure de solidité n'a pas su séparer Quod de Dafny : **aucun gain mesuré**
  en contrats solides. Par MCP, un agent n'est pas devant Dafny. Une erreur pour contrat manquant
  ne fait pas écrire de contrats à un petit modèle (14B). Un contrat trivial (`len(result) == 0`,
  `return []`) peut être complet et faux. Deux modèles ont écrit des moteurs de facturation d'environ
  300 lignes sur trois modules (24 sur 24 vérifiés et conformes à un oracle), mais règles, oracle et
  compilateur ont un seul auteur : [le plafond n'a pas été atteint](bench/runs/t9-billing/report.md).
- **Des revues externes ont trouvé des fausses preuves, corrigées.** Quatre revues adverses (par un
  modèle de langage, avec des programmes rejouables) ont trouvé entre autres un axiome de longueur
  trop fort et un z3 qui répondait `unsat` à une question satisfiable après une vérification
  interrompue (environ 1 construction sur 200 sur une famille de fichiers). La dernière, de la 0.4.0,
  n'en a trouvé aucune dans la construction par défaut. Nous ne prétendons pas qu'il n'en reste pas.

## Feuille de route

0. **Mesurer** (fait) : la vérification réduit-elle les bugs échappés, à quel coût ? Premier
   outil livré : [dafny-complete](tools/dafny-complete/).
1. **Quod 0.1** ([publié](https://github.com/quod-lang/quod/releases/latest)) : fonctions pures sur entiers, booléens,
   séquences et tuples, avec contrats, lemmes (des preuves, effacées du code généré), contrôle de
   complétude et génération Python ; depuis la 0.1.1, un serveur MCP, pour que les agents écrivent
   et vérifient du Quod comme un outil ([docs/mcp.fr.md](docs/mcp.fr.md)).
2. **Quod 0.2** ([publié](https://github.com/quod-lang/quod/releases/latest)) : une génération C# et un paquet MSBuild, pour livrer des fonctions prouvées dans des bases de code
   .NET existantes, et un dialogue plus fiable avec le solveur.
3. **Quod 0.3** ([publié](https://github.com/quod-lang/quod/releases/latest)) : modules, caractères et chaînes avec une bibliothèque standard en Quod, `i32` et `i64`, structures, énumérations, `match` et génériques.
4. **Quod 0.4** ([publié](https://github.com/quod-lang/quod/releases/latest)) : entiers C# en `long` contrôlé, limites comptées en opérations du solveur plutôt qu'en temps. Ce que cette ligne annonçait avant (capacités, contrats scellés, dictionnaires et ensembles, types raffinés généraux) passe en 0.5.
5. **Quod 0.5** : capacités (aucune autorité ambiante : une fonction ne touche la console, les
   fichiers ou le réseau qu'au travers d'une capacité qu'elle reçoit), contrats scellés,
   dictionnaires et ensembles, types raffinés généraux.
6. **Plus tard** : une génération C, vers le code natif et WASM. **Quod 2.0 sera écrit en
   Quod.**

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
