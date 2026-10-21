# Quod

*[English](README.md) · Français*

*Quod erat demonstrandum* : un langage de programmation conçu pour être **écrit par des agents IA**
et **vérifié par la machine**. Le programme arrive avec sa démonstration.

## Thèse

Le goulot d'étranglement n'est plus l'écriture du code mais la **confiance** qu'on peut lui
accorder. Tout ce qui coûte cher à un humain (contrats exhaustifs, invariants, effets déclarés)
est quasi gratuit pour un agent. Quod exige donc ce que les humains refusent d'écrire, en échange
de code vérifié plutôt que simplement plausible.

Quod est indépendant de tout LLM : le juge est un solveur (SMT), le compilateur n'appelle jamais
de modèle, et un humain peut écrire du Quod, simplement plus laborieusement.

## Contenu

| Dossier | Contenu |
|---|---|
| [tools/dafny-complete/](tools/dafny-complete/) | **Première brique, utilisable dès aujourd'hui** : contrôle de spec complète pour Dafny, avec témoins concrets des contrats sous-spécifiés |
| [bench/](bench/README.fr.md) | **Phase 0, VerifBench** : mesurer l'apport de la vérification quand des agents écrivent le code (Python vs Dafny, Opus vs Haiku) |
| [spec/](spec/) | Conception du langage : [brouillon du noyau](spec/kernel.fr.md) |
| `src/` | *(à venir)* compilateur : analyse, vérification (Z3), génération de code, en C#/.NET |

## Ce qu'on a appris jusqu'ici

*Le récit complet (en anglais) : [Green proofs, empty promises: when AI agents write their own specifications](https://dev.to/malek_aitouaret_f026758c/green-proofs-empty-promises-when-ai-agents-write-their-own-specifications-59lf) (dev.to).*

- Sommé d'écrire du Dafny *vérifié*, un modèle plus petit a produit des contrats qui se prouvent
  mais ne disent presque rien : 5 sur 8 ne contraignaient qu'une longueur, un format ou une forme.
  L'une de ces méthodes était fausse, et la preuve ne l'a pas vu.
- Un vérificateur ne garantit que ce qu'on lui demande. D'où le
  [pilier 5](spec/kernel.fr.md#5-spécifications-complètes) de Quod : le compilateur prouve que
  chaque contrat détermine un résultat **unique**, ou montre un témoin concret de deux résultats
  qu'il accepte.
- Mesuré sur 24 solutions Dafny écrites par des agents, ce contrôle trouve les 6 contrats
  sous-spécifiés, sans aucun faux verdict ([détails](bench/README.fr.md)).

## La conception en une page

1. **Contrats obligatoires** : `requires` / `ensures` sur chaque fonction, invariants sur chaque boucle.
2. **Effets par capacités** : aucune autorité ambiante. Une fonction ne peut toucher la console,
   les fichiers, l'horloge ou le réseau que si elle *reçoit* une capacité pour cela : sa
   signature dit tout ce qu'elle peut faire.
3. **Types raffinés** : `type Percent = i32 where 0 <= _ && _ <= 100`.
4. **Diagnostics pour agents** : JSON structuré avec contre-exemples concrets.
5. **Spécifications complètes** : un contrat sous-spécifié ne compile pas, sauf liberté déclarée
   par une clause `loose`.

```rust
fn greet(out: Console, name: str)
  requires len(name) > 0
  ensures out.written == old(out.written) + [greeting(name) + "\n"]
{
  out.write_line(greeting(name))
}

fn main(sys: System) {
  greet(sys.console, "world")
}
```

## Feuille de route

0. **Mesurer** (fait, voir [bench/](bench/README.fr.md)) : la vérification réduit-elle les bugs
   échappés, à quel coût ? Premier outil livré : [dafny-complete](tools/dafny-complete/).
1. **Noyau minimal** : front-end en C#, conditions de vérification vers Z3, génération de C# ;
   fonctions pures avec contrats et contrôle de complétude.
2. **Interface agents** : diagnostics JSON avec contre-exemples et témoins, serveur MCP.
3. **Capacités** et leur runtime.
4. **Performance** : backends LLVM/MLIR et WASM.

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
  Phase 0.
- **Qualité des spécifications écrites par des LLM** : le test symbolique de spécifications
  Dafny de Lahiri ([FMCAD 2024](https://arxiv.org/abs/2406.09757)) est l'ancêtre direct de la
  recherche de témoins de `dafny-complete` ; voir aussi nl2postcond, Clover et le programme
  « intent formalization », résumés dans [docs/related-work.md](docs/related-work.md).
- **Unison** : code adressé par contenu.
- **[Warrant](https://github.com/mv2a/warrant)** : protocole de preuves pour du code écrit par des
  agents, agnostique du langage. Très proche dans l'intention ; Quod se place une couche en
  dessous (le langage lui-même) et pourrait en être un producteur de preuves.
