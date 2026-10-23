# Les tâches VerifBench en Quod

[English](README.md)

Les six tâches VerifBench sans chaînes de caractères, écrites en Quod 0.1 à la main (étape 6 du
[périmètre 0.1](../../spec/quod-0.1.fr.md)), avant de demander à un agent de les écrire à partir de
la seule grammaire. Chacune est vérifiée, compile en Python, et passe les tests cachés de VerifBench
(les mêmes tests que pour les bras Python et Dafny de la phase 0).

| Tâche | Lignes | Obligations | Contrat déterminé | Indications | Tests cachés |
|---|---|---|---|---|---|
| [binary_search](binary_search/solution.quod) | 22 | 29 | ✅ (avec `loose`) | aucune | 510/510 |
| [merge_intervals](merge_intervals/solution.quod) | 89 | 176 | ⚠️ non décidé | 6 assert, 2 lemmes | 508/508 |
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
