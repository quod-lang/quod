# Entrées-sorties et capacités (0.6) : note de conception

État : **étape 1 implémentée** (2026-11-12, non publiée) : `Console` en sortie seulement, `console.say` et `console.written`, usage unique contrôlé (`src/Quod/Capabilities.fs`), évaluateur, Python, C#, `quod run`, `quod_run` du serveur MCP. Écarts avec la proposition ci-dessous : la capacité est une `struct Console { lines }` de la bibliothèque standard (`stdlib/console.quod`), dont le modèle est la liste des lignes, et c'est le module `console` qui est remplacé dans le code généré (Python : une classe qui écrit sur un flux ; C# : une classe `ConsoleModule.Console` sur un `TextWriter`, et non une interface) ; la syntaxe est l'option A (la console passée et rendue) ; `quod run` exécute avec l'évaluateur et affiche les lignes à la fin. **Étape 2 implémentée** (2026-11-13) : `console.read_line(c)` rend la paire (console suivante, `option.Option<string>`) ; le modèle a un second champ, les lignes à lire (`console.pending(c)`, lisible dans les contrats seulement), qui est une séquence quelconque pour qui exécute le programme. Conséquence à connaître : un contrat doit dire ce qu'il fait de `pending` (`pending(result) == pending(c)` pour un programme qui n'écrit que), sinon le contrôle de complétude voit deux résultats possibles. `quod run` lit l'entrée standard en entier avant l'exécution ; Python et C# lisent un flux (`Console(flux, source)`, `new Console(writer, reader)`). Pas encore : l'essai d'agent, les fichiers.

## Le problème

Une fonction Quod est pure : elle calcule un résultat à partir de ses arguments, et l'hôte (Python ou C#) fait les entrées-sorties. C'est suffisant pour le cas visé (des règles métier appelées depuis une application), mais cela exclut deux choses : un programme Quod complet (un outil en ligne de commande, un script écrit par un agent), et un contrat qui dise ce qu'une fonction **écrit** ou **lit**. Le README annonce des *capacités* : une fonction ne touche la console, les fichiers ou le réseau que par une capacité qu'elle reçoit. Cette note dit ce que cela peut vouloir dire de précis, et par quoi commencer.

## Ce que la 0.6 ne doit pas casser

1. **Une fonction sans capacité en paramètre reste pure**, et c'est vérifié par construction. C'est déjà vrai ; c'est aussi la garantie la plus utile pour du code écrit par un agent : « cette fonction ne peut pas écrire un fichier » se lit dans sa signature.
2. **Les preuves portent sur un modèle**, et le texte le dit : l'implémentation d'une capacité (le vrai disque, le vrai réseau) n'est pas vérifiée, comme l'hôte ne l'est pas aujourd'hui.
3. **Pas de dépendance dans le code généré** : en C#, une capacité est une interface déclarée dans le fichier généré, que l'appelant implémente (et peut remplacer dans ses tests) ; en Python, un objet qui a les méthodes attendues.

## Le modèle proposé

Une capacité est un type prédéfini, dont l'état **abstrait** est visible des contrats :

| Capacité | État abstrait | Opérations |
|---|---|---|
| `Console` | `written(c): seq<string>` (lignes écrites), `pending(c): seq<string>` (lignes encore à lire) | `say(c, s)`, `read_line(c)` |
| `Files` | `contents(f): map<string, string>` | `read_file(f, path)`, `write_file(f, path, text)` |

Une opération qui change le monde **rend la capacité suivante** : `say(c, s)` a pour contrat `written(result) == written(c) + [s]`. Rien ne change sur place, ce qui garde le vérificateur tel qu'il est : pas de cadre (`modifies`), pas d'alias.

**La règle qui rend ce modèle honnête : une capacité s'utilise une fois.** Après `let c2 = say(c, "a")`, la valeur `c` est consommée ; la relire est une erreur de type (« `c` a déjà été passée »). Sans cela, `written(c)` parlerait d'un monde qui n'existe plus et la preuve serait fausse. C'est un contrôle de type simple (usage affine, sur les variables de type capacité), sans notion de durée de vie.

Les opérations qui peuvent échouer rendent `Result` ou `Option` (la bibliothèque `option.quod` existe) : `read_file` rend `Option<string>`, et son contrat dit que le résultat est `Some` exactement quand le chemin est dans `contents`. Les opérations dont le résultat vient de l'extérieur (réseau, horloge, hasard) rendent une valeur **quelconque** du bon type : le contrat ne peut rien en supposer, et un `requires` dessus est refusé.

## Syntaxe : la question ouverte

Écrire `let c = say(c, ...)` à chaque ligne est lourd. Deux options :

- **A, explicite** : on passe et on rend la capacité, `fn report(c: Console, total: i64) -> Console`. Verbeux, mais rien de nouveau dans le langage.
- **B, paramètre `mut`** : `fn report(mut c: Console, total: i64)`, avec `say(c, "...");` comme instruction qui remplace `c`, et `old(c)` dans les contrats. C'est un sucre pour A : le vérificateur traduit en A. Plus lisible pour un agent comme pour un humain.

Je propose de **commencer par A** (aucun nouveau mot-clé, aucune interaction avec les boucles à trancher), de faire écrire quelques programmes réels, et de décider de B sur pièces.

## Ce qu'il faut toucher

- **Typecheck** : types capacité, usage unique (affine), `Option` pour l'échec.
- **Vcgen** : les opérations sont des fonctions « externes » dont le contrat est admis (un seul endroit pour le modèle : un petit fichier de contrats prédéfinis, relu avec soin, parce que c'est ce que la preuve suppose).
- **Évaluateur** : un monde simulé en mémoire (console, fichiers), pour que les contre-exemples par exécution marchent encore.
- **Python et C#** : l'interface, et l'appel. Complétude des contrats : le contrôle « deux résultats différents » doit aussi porter sur l'état rendu (`written(result)`), sinon un contrat qui n'écrit rien de précis passerait.
- **`quod run`** : un `main(c: Console) -> Console` branché sur l'entrée et la sortie standard.
- **MCP** : `quod_run` fournit la console simulée et rend ce qui a été écrit.

## Étapes proposées

1. **`Console` en sortie seulement**, avec l'usage unique, le modèle `written`, l'évaluateur, Python, C#, `quod run`. C'est la plus petite tranche qui prouve l'idée de bout en bout.
2. **Lecture** (`read_line`, `pending`) : premier cas où l'extérieur donne une valeur ; on voit si le modèle tient.
3. **`Files`**, avec la table `map<string, string>` (c'est ce que les dictionnaires de la 0.5 préparent).
4. Plus tard, et seulement sur un besoin : horloge, hasard, réseau.

Entre les étapes 1 et 2, **un essai d'agent** (coûteux : à faire seulement sur votre feu vert) : un agent écrit-il un petit programme avec sortie, contrat compris, depuis la référence seule ? Si non, rien d'autre ne sert de continuer.

## Ce que je déplace

Le README met aussi dans la 0.6 les *contrats scellés* et les *types raffinés généraux*. Je propose de les passer à la 0.7 : ce sont deux sujets différents, la 0.6 serait trop grosse, et chacun a sa propre question de preuve.

## Doutes à dire

- Le gain est surtout **pour les programmes complets** ; pour le cas métier appelé depuis C#, la 0.5 suffit. Si ce cas est celui qui compte, la 0.6 peut attendre.
- L'usage unique est un contrôle de plus à expliquer à un agent ; s'il génère trop d'erreurs, B devient nécessaire plus tôt.
- Le modèle de fichiers ignore les droits, les accès concurrents, l'ordre des écritures entre processus : le texte de la spécification doit le dire.
