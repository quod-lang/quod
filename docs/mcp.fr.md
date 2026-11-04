# Quod comme outil pour les agents IA (MCP)

*[English](mcp.md) · Français*

`quod mcp` est un serveur [Model Context Protocol](https://modelcontextprotocol.io) : un agent
vérifie, compile et exécute des programmes Quod à travers lui, sans shell, et y lit la référence du
langage. Il fait partie du binaire `quod` de la
[version publiée](https://github.com/quod-lang/quod/releases/latest), avec z3 à côté : rien d'autre à
installer.

## Outils

| Outil | Ce qu'il fait |
|---|---|
| `quod_check` | Types, preuves (z3) et complétude d'un programme donné par `source` (son texte) ou `path`. Renvoie les diagnostics, avec contre-exemples, et une ligne de résumé qui commence par `verified` ou `rejected`. Options : `timeout`, `budget`. |
| `quod_build` | Vérifie, puis renvoie le module Python généré, sous forme de texte (aucun fichier écrit). Seul un programme vérifié est compilé, sauf si `runtime_checks` vaut vrai. |
| `quod_run` | Exécute une fonction sur des arguments donnés (nombres, booléens, tableaux JSON), en vérifiant au passage chaque assertion, invariant, borne et contrat. Renvoie le résultat, ou l'obligation qui échoue, avec son texte (et la valeur renvoyée, pour une postcondition). |
| `quod_reference` | La référence du langage, ou l'une de ses sections (`section` : `Hints and lemmas`, `Contract style`...). Aussi une ressource : `quod://reference`. |

Chaque outil renvoie un texte pour l'agent, et les mêmes faits en JSON (`structuredContent`).

## Installation

Remplacer `/chemin/vers/quod` par l'endroit où la version publiée a été décompressée (`quod.exe`
sous Windows).

**Claude Code**

```bash
claude mcp add quod -- /chemin/vers/quod mcp
```

**Les clients qui lisent `mcpServers`** (Claude Desktop, Cursor dans `.cursor/mcp.json`, Gemini
CLI, un `.mcp.json` de projet) :

```json
{
  "mcpServers": {
    "quod": { "command": "/chemin/vers/quod", "args": ["mcp"] }
  }
}
```

**VS Code** (`.vscode/mcp.json`) :

```json
{
  "servers": {
    "quod": { "type": "stdio", "command": "/chemin/vers/quod", "args": ["mcp"] }
  }
}
```

**Codex CLI** (`~/.codex/config.toml`) :

```toml
[mcp_servers.quod]
command = "/chemin/vers/quod"
args = ["mcp"]
```

Le serveur parle MCP sur stdio (un message JSON-RPC par ligne). Il ne demande aucune variable
d'environnement : z3 est trouvé à côté de `quod` (ou dans `QUOD_Z3`, puis dans le `PATH`). Les
arguments `path` sont relatifs au dossier de travail du serveur : celui dans lequel le client le
lance, en général le projet.

Une vérification à travers le serveur a un **budget de temps de 60 s** par défaut, car un agent
attend l'appel d'outil (la ligne de commande a 300 s) : les obligations restantes quand il est
épuisé sont signalées `not-attempted`, pas comme des échecs. Un agent peut en demander plus avec
l'argument `budget`, et `quod mcp --budget 120` change la valeur par défaut (`--timeout` aussi,
10 s par obligation).

`quod mcp --require-contracts` fait une erreur d'une fonction sans contrat ou d'un `loose` qui accepte
tout résultat : un agent ne peut plus s'arrêter sur un fichier vérifié parce qu'il n'énonce rien. L'option se règle sur le serveur :
l'agent n'a aucun argument pour la désactiver.

Les appels d'outils s'exécutent un à la fois, pendant que le serveur continue de lire : `ping`,
`tools/list` et les ressources reçoivent une réponse immédiate, `notifications/cancelled` arrête
l'appel qu'il désigne (z3 est arrêté, et aucune réponse n'est envoyée), et un appel qui fournit un
`progressToken` reçoit des notifications de progression : au début et à la fin de chaque fonction et
de chaque contrôle de complétude, et quand un essai du solveur dure depuis une seconde
(`f: invariant #2, solver, up to 10 s`).

## Pour l'agent : une section pour AGENTS.md ou CLAUDE.md

La copier dans le fichier d'instructions du projet, et adapter la dernière étape. Elle est en
anglais, la langue que les agents suivent le plus sûrement.

```markdown
## Quod: proved functions

When asked to write a function in Quod, or a function that must be proved correct:

1. Read the language reference once with `quod_reference`.
2. Write the function with a contract that determines its result: state what the result is
   (bounds, order, membership...), not how to compute it. Declare an intended freedom with
   `loose`; never weaken a contract to make it pass.
3. Call `quod_check` until the summary starts with `verified`. A counterexample gives inputs
   that break the code or the contract: fix one or the other. When the solver gives up without a
   counterexample, add an `assert`, an invariant or a `lemma` (see the reference).
4. Call `quod_build` and save the Python module next to the code that uses it.
5. Tell me which functions the contracts rely on (the summary lists them under "to review with
   the contracts"), and every `loose`: the proofs show that the code agrees with them, not that
   they say what was meant.
```
