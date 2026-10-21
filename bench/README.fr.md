# VerifBench, Phase 0

*[English](README.md) · Français*

**Question :** quand un agent écrit du code, le forcer à le *prouver* (contrats + vérificateur
SMT) réduit-il les bugs qui passent entre les mailles, et à quel coût ?

Avant de concevoir un langage axé vérification et pensé pour les agents, on teste l'hypothèse avec
un outil existant : **Dafny** (vérification par Z3, compile vers Python), face à **Python** simple.

## Protocole

- **Deux suites de 8 tâches algorithmiques courtes**, riches en cas limites
  ([tasks.py](verifbench/tasks.py), [tasks_hard.py](verifbench/tasks_hard.py)) :
  - *base* : `binary_search`, `merge_intervals`, `rle_encode`, `parse_int`, `bounded_queue`,
    `max_subarray`, `rotate`, `balanced` ;
  - *difficile*, choisie parce que les LLM y trébuchent classiquement : `days_between` (années
    bissextiles grégoriennes), `utf8_valid` (formes trop longues, surrogates), `glob_match`
    (échappements), `lru_cache`, `topo_sort` (plus petit ordre lexicographique), `justify`,
    `add_big` (retenues, `-0`), `normalize_path`.
- **Même spécification en langage naturel** pour les deux bras ; seule la langue cible change.
- **Bras `python`** : l'agent écrit `solution.py` et peut exécuter ses propres tests.
- **Bras `dafny`** : l'agent écrit `solution.dfy` avec `requires` / `ensures` / invariants et doit
  obtenir `dafny verify` OK. Triches détectées : `assume`, `{:axiom}`, `{:verify false}`, `{:extern}`.
- **Tests cachés identiques** : environ 500 cas par tâche (cas limites + aléatoires à graine fixe),
  comparés à un oracle. La solution Dafny est compilée en Python et passe par le même banc.
- L'agent travaille dans un dossier temporaire hors du dépôt, sans accès aux tests.
- Agent : Claude Code (`claude -p`), modèles Opus et Haiku. Le banc accepte tout agent en ligne
  de commande qui lit son prompt sur stdin (`--agent-cmd`).

## Métriques

| Métrique | Sens |
|---|---|
| **Accepté** | ce que l'agent livrerait : le fichier existe (et, pour Dafny, il est vérifié sans triche) |
| **Bug échappé** | accepté mais échoue à au moins un test caché : *la métrique clé* |
| Tours, coût, durée | le prix payé pour la vérification (coût = estimation au tarif API) |

## Résultats

Un seul essai par combinaison (tâche, bras, modèle) : ce sont des signaux, pas des statistiques.

**Suite de base** (`runs/pass1`, modèle par défaut) : 16 runs sur 16 passent tous les tests
cachés, dans les deux bras. Effet plafond : les tâches étaient trop faciles pour départager les
bras. Dafny a coûté environ 1,6× plus, et 2,8× plus de temps.

**Suite difficile** (`runs/hard1`) :

| Modèle / bras | Accepté | Tests cachés 100 % | **Bug échappé** | Tours | Coût | Durée |
|---|---|---|---|---|---|---|
| Opus / Python | 8/8 | 8/8 | **0** | 3,5 | 0,14 $ | 17 s |
| Opus / Dafny | 8/8 | 8/8 | **0** | 3,9 | 0,22 $ | 46 s |
| Haiku / Python | 8/8 | 7/8 | **1** | 11,1 | 0,15 $ | 106 s |
| Haiku / Dafny | 8/8 | 7/8 | **1** | 35,6 | 0,45 $ | 255 s |

- Haiku / Python : `normalize_path("a/..")` renvoyait `".."` au lieu de `"."`.
- Haiku / Dafny : `lru_cache` était **prouvé et faux**. Sa seule postcondition était
  `|out| == CountGets(ops, |ops|)` : la longueur de la sortie, rien sur son contenu.

C'est ce dernier cas qui a mené au contrôle de complétude ci-dessous, et au pilier 5 de Quod.

## Complétude des spécifications (pilier 5)

`python -m verifbench.completeness runs/pass1 runs/hard1` génère pour chaque solution un lemme
`ensures(a) ∧ ensures(b) ⇒ a == b` et demande à Dafny de le prouver sans aide.
`python -m verifbench.witness` cherche ensuite des témoins : sur de petites entrées concrètes, il
prend la bonne réponse `a` et des réponses voisines `b`, et fait **prouver** par Dafny
`Post(x, a)` et `Post(x, b)`. Un témoin trouvé est donc certain.

| Verdict | Nb | Cas |
|---|---|---|
| Unicité prouvée | 15 | Opus : 7/8 sur la suite difficile ; base : 5/8 |
| **Sous-spécifié, témoin trouvé** | 5 | tous chez Haiku : `lru_cache` (vrai bug), `add_big`, `justify`, `normalize_path`, `topo_sort` |
| Liberté légitime (relèverait de `loose`) | 1 | `binary_search` (doublons) |
| Non conclu (complet, mais l'unicité demande une induction) | 3 | `merge_intervals`, `rle_encode`, `add_big` Opus |

| Sous-spécifié | Témoin : une entrée, deux résultats acceptés |
|---|---|
| `binary_search` | `([1,1,1], 1)` : `1` et `2` |
| `add_big` Haiku | `"0" + "0"` : `"0"` et `"1"` |
| `justify` Haiku | `(["a"], 1)` : `["a"]` et `[]` |
| `lru_cache` Haiku | un `get` sur un cache vide : `[-1]` et `[0]` |
| `normalize_path` Haiku | `""` : `"."` et `".x"` |
| `topo_sort` Haiku | un nœud, aucune arête : `[0]` et `[]` |

Séparation nette : les 6 contrats vraiment sous-spécifiés ont tous un témoin, les 3 « non
conclu » n'en ont aucun. Quatre des cinq contrats quasi vides de Haiku portaient sur du code
*correct* : les preuves étaient vertes mais ne garantissaient presque rien. Ces scripts sont
devenus l'outil autonome [dafny-complete](../tools/dafny-complete/), qui fonctionne sur
n'importe quel fichier `.dfy` et retrouve les mêmes verdicts sans oracle (il exécute la méthode
elle-même).

## Utilisation

```bash
python -m verifbench.selfcheck                        # les tests cachés discriminent-ils ?
python -m verifbench.run --suite hard --models opus,haiku --trials 3
python -m verifbench.run --tasks rotate --arms dafny --agent-cmd "<tout agent lisant stdin>"
python -m verifbench.report runs/<stamp>/results.jsonl
python -m verifbench.rescore runs/<stamp>/results.jsonl --where task=X,model=Y,arm=dafny
```

`rescore` réévalue des runs existants après une correction *du banc* ; il ne donne jamais de
seconde chance à un agent.

Prérequis : Python ≥ 3.10 ; pour le bras Dafny, Dafny 4.x (`dotnet tool install --global dafny`)
avec Z3 ; un agent en ligne de commande qui lit son prompt sur stdin (par défaut `claude -p`).

## Auto-contrôle

Chaque tâche a une solution correcte (100 % attendu) et une solution buguée « typique d'agent »
(off-by-one, cas tout-négatif, `int()` trop permissif, modulo oublié, années séculaires, `-0`...)
qui doit être attrapée : **32/32**. Le bras Dafny est validé de bout en bout (vérification,
traduction Python, tests cachés) avec des solutions de référence prouvées dans
[reference/dafny/](reference/dafny/).

Note Windows : l'outil .NET `dafny` n'embarque pas Z3 ; placer `z3-4.12.1.exe` dans
`<dossier de Dafny.dll>/z3/bin/`.
