# Les tâches VerifBench en Quod

[English](README.md)

Les six tâches VerifBench sans chaînes de caractères, écrites en Quod 0.1 à la main (étape 6 du
[périmètre 0.1](../../spec/quod-0.1.fr.md)), avant de demander à un agent de les écrire à partir de
la seule grammaire. Chacune est vérifiée, compile en Python, et passe les tests cachés de VerifBench
(les mêmes tests que pour les bras Python et Dafny de la phase 0).

| Tâche | Lignes | Obligations | Contrat déterminé | Indications | Tests cachés |
|---|---|---|---|---|---|
| [binary_search](binary_search/solution.quod) | 22 | 29 | ✅ (avec `loose`) | aucune | 510/510 |
| [merge_intervals](merge_intervals/solution.quod) | 87 | 168 | ⚠️ non décidé | 6 assert, 2 lemmes | 508/508 |
| [rle_encode](rle_encode/solution.quod) | 39 | 55 | ⚠️ non décidé | aucune | 506/506 |
| [bounded_queue](bounded_queue/solution.quod) | 49 | 69 | ✅ | 3 assert | 505/505 |
| [max_subarray](max_subarray/solution.quod) | 31 | 64 | ✅ | aucune | 506/506 |
| [rotate](rotate/solution.quod) | 6 | 10 | ✅ | aucune | 508/508 |

Les lignes excluent commentaires et lignes vides. Les deux ⚠️ sont des formes canoniques (un codage
par plages, une liste d'intervalles disjoints triés) : leur unicité demande une récurrence, et la
vérification dit « non décidé » (un avertissement) plutôt que de deviner. En phase 0, notre contrôle
de complétude des solutions Dafny ([dafny-complete](../../tools/dafny-complete)) avait donné la même
fausse alerte sur ces deux tâches. Pour comparaison, la solution
Dafny écrite par Opus pour merge_intervals fait 193 lignes.

Pour en lancer une :

```bash
quod build bench/quod/rotate/solution.quod -o out/rotate
cd bench
python -m verifbench.hidden --task rotate --arm python --dir ../out/rotate
```

## Un agent les écrit

Passage [quod1](../runs/quod1) : le modèle par défaut de Claude Code, un essai par tâche, avec pour
seuls documents la [référence du langage](../runs/quod1/work/rotate__quod__default__0/QUOD.md) (la
partie langage du périmètre 0.1, sans son exemple) et l'énoncé de la tâche.

| Tâche | Temps | Tours | Style du contrat | Tests cachés |
|---|---|---|---|---|
| binary_search | 26 s | 6 | propriétés, `loose` trouvé par l'agent | 510/510 |
| merge_intervals | 18 min | 26 | modèle (insertion récursive) | 508/508 |
| rle_encode | 25 s | 4 | modèle (codage récursif) | 506/506 |
| bounded_queue | 23 s | 4 | modèle (la file, pas à pas) | 505/505 |
| max_subarray | 48 s | 7 | propriétés | 506/506 |
| rotate | 17 s | 4 | recopie (l'ensures est le corps) | 508/508 |

Les six sont vérifiées et passent les tests cachés (environ 1,70 USD en tout). Aucun contrat faible
n'est passé : la vérification de complétude les rejette. Mais le contrat déterminé le plus court est
`result == <le corps>`, ou `result == f(...)` pour un `f` récursif qui calcule la même chose : quatre
contrats sur six disent comment calculer le résultat, pas ce qu'il est. D'où le
[style des contrats](../../spec/quod-0.1.fr.md#style-des-contrats) que `quod check` signale désormais,
avec un avertissement pour un corps recopié.

Un modèle plus petit, Haiku, un essai par tâche, deux fois : [quod2-haiku](../runs/quod2-haiku)
avec le compilateur d'alors, puis [quod3-haiku](../runs/quod3-haiku) après la revue externe
(lemmes, contre-exemples par exécution, notes sur les contrats) et une référence du langage plus
longue.

| Tâche | quod2-haiku | quod3-haiku |
|---|---|---|
| binary_search | vérifié, complétude non décidée | vérifié, déterminé, 71 s |
| merge_intervals | vérifié, non décidé | vérifié, non décidé, 28 min |
| rle_encode | vérifié **sans aucun ensures** (limite de temps atteinte) | vérifié, non décidé |
| bounded_queue | rejeté | vérifié, déterminé, 84 s |
| max_subarray | rejeté | vérifié, non décidé, 46 s |
| rotate | vérifié, par un modèle | vérifié, déterminé, par propriétés |

quod2-haiku a trouvé les trous du contrôle de complétude (un `loose` qui accepte tout, aucun
ensures), désormais signalés. Dans quod3-haiku, les six se vérifient et passent les tests cachés,
trois avec un contrat déterminé, pour 0,59 USD au lieu de 2,83 ; l'agent a écrit des `lemma` de
lui-même dans quatre tâches. Un essai chacun, et deux changements à la fois (le compilateur et la
référence) : une tendance, pas une mesure.

Puis le même modèle à travers le serveur MCP : [quod4-haiku-mcp](../runs/quod4-haiku-mcp) (le bras
`quod-mcp` : ni shell ni QUOD.md, seulement les fichiers et les quatre outils de `quod mcp`), avec le
même compilateur que quod3-haiku.

| | quod3-haiku (shell) | quod4-haiku-mcp (MCP) |
|---|---|---|
| Vérifiés, et passent les tests cachés | 6/6 | 6/6 |
| Contrat déterminé | 3/6 | 6/6 (merge_intervals et rle_encode par un modèle) |
| Tours par tâche | 7 à 42 | 4 à 16 |
| Temps, coût | 47 min, 0,59 USD | 7 min, 0,08 USD |

L'agent ne tâtonne plus avec un shell, des chemins et des fichiers temporaires : il appelle
`quod_check` et lit une réponse structurée. Un essai par tâche là encore : une tendance, pas une
mesure.

### Trois essais, Dafny, et un autre fournisseur

[t6-haiku](../runs/t6-haiku) : Haiku, trois essais des six tâches dans chacun des trois bras, avec
le compilateur 0.1.3. Le bras Dafny est celui de la phase 0 (shell, `dafny verify`) ; ses contrats
ont ensuite été soumis à [dafny-complete](../../tools/dafny-complete/)
([résultats](../runs/t6-haiku/dafny-complete.jsonl)).

| | quod (shell) | quod-mcp | dafny |
|---|---|---|---|
| Acceptés par le vérificateur | 18/18 | 16/18 | 18/18 |
| Passent tous les tests cachés | 18/18 | 17/18 | 18/18 |
| Contrat déterminé | 17/18 | 12/18 | 9/18 (dafny-complete) |
| Style des contrats | 10 propriétés, 8 modèles | 12 propriétés, 6 modèles | — |
| Temps, coût (18 essais) | 54 min, 0,54 USD | 71 min, 1,15 USD | 17 min, 0,24 USD |

- **Aucun bug échappé, dans aucun bras** : toute solution acceptée passe les tests cachés.
- **L'avantage de MCP vu dans quod4-haiku-mcp ne tient pas** sur trois essais. À travers MCP,
  l'agent écrit plus de contrats par propriétés, plus durs à prouver et à déterminer : deux
  solutions gardent des obligations non conclues (merge_intervals, rotate), cinq contrats une
  complétude non conclue.
- **Dafny est plus rapide et moins cher**, et ses contrats en disent moins. Sur les 18,
  dafny-complete en trouve 3 sous-spécifiés (tous binary_search : n'importe quel indice d'un
  doublon est accepté, ce que la tâche permet ; Dafny n'a pas de `loose` pour le dire) et ne peut
  pas en décider 6 (merge_intervals, rle_encode). En Quod, le contrôle de complétude fait partie de
  l'acceptation : l'agent continue tant qu'elle n'est pas décidée.

[t6-qwen14b](../runs/t6-qwen14b) : un autre fournisseur, Qwen 2.5 Coder 14B exécuté en local par
Ollama, dans le bras `quod-mcp` (l'agent est [ollama_agent.py](../verifbench/ollama_agent.py), un
client MCP avec les mêmes outils), trois essais des six tâches. **0/18** : chaque essai s'arrête à
40 tours, 13 des 18 fichiers finaux sur une erreur de syntaxe. La plupart sont des habitudes de
Dafny : clauses de contrat dans le corps, `;` après une clause, `for`, `let result`, `return` dans
un ensures. L'analyseur nomme désormais chacune et dit quoi écrire à la place.

[t6-qwen14b-hints](../runs/t6-qwen14b-hints), le même passage avec ces messages : **0/18 encore**.
Les habitudes que les messages nomment disparaissent presque des fichiers finaux (5 clauses dans
le corps deviennent 0, 3 `let result` deviennent 0), mais d'autres prennent leur place (une
expression au milieu d'un bloc, `:` pour `in`, `|s|` pour `len(s)`), et 3 fichiers mettent encore
un `;` après une clause. Le modèle corrige l'erreur qu'on lui montre et en commet une autre ; 15
des 18 fichiers finaux finissent sur une erreur de syntaxe. Un langage qu'aucun modèle n'a vu
demande, pour l'instant, un modèle capable de suivre une référence qu'il lit pour la première fois.

## Ce que leur écriture a changé dans le vérificateur

- **Les séquences sont axiomatisées** (comme le fait Dafny), au lieu d'utiliser la théorie des
  séquences de Z3, qui ne transportait pas les faits quantifiés à travers `r[..n] + [x]` et rendait
  les preuves instables.
- **Le corps d'une boucle est vérifié sans les faits sur les valeurs d'avant la boucle**, qui
  égaraient Z3 (un dépassement de temps est devenu une preuve en 0,1 s).
- **Une obligation qui échoue dans le mode incrémental de Z3 est retentée sur un solveur neuf** ;
  les deux modes réussissent sur des requêtes différentes.
- Les littéraux de tuples et de séquences acceptent des parties `nat` : `(x, c + 1)` là où
  `(int, nat)` est attendu.

Et dans la manière d'écrire du Quod : [indications et lemmes](../../spec/quod-0.1.fr.md#indications-et-lemmes).

## Petits bugs : un banc de mutants

[mutants.py](../verifbench/mutants.py) modifie un opérateur ou une constante dans le code d'un
programme vérifié (jamais dans ses contrats), et note comment `quod check` le rejette : avec un
contre-exemple, sans, ou pas du tout (un mutant équivalent, ou un bug que le contrat ne voit pas).
Un échantillon tiré avec une graine fixe, 10 mutants par programme, sur les six solutions
ci-dessus et les deux programmes d'une revue externe ([isqrt](../review/isqrt.quod),
[prefix_sums](../review/prefix_sums.quod)) ; 64 mutants valides.

| Compilateur | Réfutés, avec contre-exemple | Rejetés, sans contre-exemple | Bloqués | Survivants | Temps médian de rejet |
|---|---|---|---|---|---|
| avant ([journal](../runs/mutants-before.log)) | 7 | 48 | 2 | 7 | 27 s |
| avec les contre-exemples par exécution ([journal](../runs/mutants-after.log)) | 57 | 0 | 0 | 7 | 1,3 s |

Avant de solliciter Z3, le compilateur exécute désormais chaque fonction sur de petites entrées
qui satisfont son `requires`, en vérifiant chaque obligation au passage : une obligation violée est
un contre-exemple certain, trouvé en quelques millisecondes là où Z3 dépassait souvent le temps.
Les deux vérifications bloquées venaient de Z3, qui ne respectait pas sa propre limite de temps
(plus de 15 minutes) ; un chien de garde remplace désormais le processus. Les 7 survivants sont
tous des mutants équivalents (`>=` pour `>` là où les deux branches coïncident, la valeur d'une
fonction modèle sur une entrée vide, un lemme qui s'arrête un pas plus tard...).

**Des entrées trouvées par le solveur.** Une contre-revue externe a trouvé la famille que ces
exécutions manquent : les bugs dont l'entrée doit satisfaire un `requires` quantifié, ce que des
entrées aléatoires ne font presque jamais, et que le solveur ne trouve pas non plus.
[quantified.quod](../mutants/quantified.quod) en a trois (au moins quatre valeurs strictement
croissantes, à partir de 10) ; 30 mutants :

| Compilateur | Réfutés, avec contre-exemple | Rejetés, sans contre-exemple | Survivants | Temps médian de rejet |
|---|---|---|---|---|
| entrées aléatoires seules ([journal](../runs/mutants-quantified-before.log)) | 0 | 29 | 1 | 10,7 s |
| et entrées trouvées par le solveur ([journal](../runs/mutants-quantified-after.log)) | 28 | 1 | 1 | 0,2 s |

Quand peu d'entrées aléatoires satisfont le `requires`, le solveur en trouve, à longueur fixée,
où les quantificateurs se déplient. Sur les huit programmes ci-dessus
([journal](../runs/mutants-solver-inputs.log)), rien ne change : mêmes verdicts, même temps.

**Mesuré et non retenu : le dépliage borné (carburant).** Dafny déplie une fonction récursive un
nombre borné de fois. Essayé avec 2 niveaux ([patch](../runs/fuel-experiment.patch),
[journal](../runs/mutants-fuel2.log)), sur les mêmes mutants : autant de réfutés (51 des 55 encore
dans l'échantillon), 13 % de temps en moins au total, et ce gain venait du contrôle de complétude
qui abandonnait plus tôt sur rle_encode, avec le même verdict. Mais une preuve correcte a échoué :
l'invariant `forall i in 0..k: sum(xs, i, k) <= here` de max_subarray, même avec 3 niveaux, car le
`sum` déplié est un terme d'un niveau inférieur que l'invariant quantifié ne reconnaît pas. Cela a
aussi fait rejeter un mutant équivalent. Le dépliage non borné reste.
