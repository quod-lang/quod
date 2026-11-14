# Essai humain : voir Quod depuis la place de l'utilisateur

Jusqu'ici, Quod n'a été essayé que par ses auteurs et par des agents sur des tâches faciles. Ce document prépare un essai différent : **vous, un peu en retrait, qui faites écrire un programme à un agent et jugez ce que vous voyez**. Vous n'avez pas besoin de connaître la syntaxe : l'agent l'écrit, vous lisez surtout les **contrats** (les lignes `requires` et `ensures`), qui disent ce que le programme garantit. C'est exactement la place de la personne pour qui Quod est fait.

## Mise en place (5 minutes)

1. Téléchargez la dernière version (zip Windows) sur la page des releases, dézippez-la dans un dossier, par exemple `C:\outils\quod`. Z3 est dedans.
2. Dans un dossier de travail vide, donnez l'outil à Claude Code :

```bash
claude mcp add quod -- C:\outils\quod\quod.exe mcp
```

3. Ouvrez Claude Code dans ce dossier. L'agent dispose maintenant de `quod_reference` (le manuel du langage), `quod_check`, `quod_run` et `quod_build`.

## Le prompt de départ

À adapter au besoin choisi, mais gardez cette forme :

> Écris en Quod, dans le fichier `programme.quod`, un programme qui fait ceci : *(décrivez le besoin en quelques phrases, comme à un collègue)*. Quod est un langage vérifié : tu as le manuel avec `quod_reference`, et `quod_check` prouve les contrats. Ajoute des contrats (`requires`, `ensures`) qui disent précisément ce que le programme garantit, et arrête-toi quand `quod_check` est vert. Ensuite explique-moi, en français et sans jargon, ce que dit chaque contrat.

La dernière phrase est la plus importante pour vous : c'est elle qui vous permet de **juger les contrats sans lire le code**.

## Quel besoin choisir ?

Un besoin à vous, inventé ou tiré de vos projets personnels, **pas du travail** (pas de règle réelle de l'employeur). Trois pistes, par ordre d'intérêt :

1. **Une règle de votre jeu** (Ouï-dire) : le calcul d'un stock, de rations, d'une saison, que vous aimeriez voir prouvé correct, avec un C# à intégrer dans le projet Godot. C'est le cas qui vous parle et qui exerce la sortie C#.
2. **Un petit outil de fichiers** : lire un fichier texte de notes ou de dépenses, calculer des totaux par catégorie, écrire un rapport. Exerce les fichiers, les chaînes et les dictionnaires (0.7).
3. **Une règle de remise ou de tarif inventée**, comme celles des essais précédents (le terrain le mieux connu de Quod, donc le moins instructif).

## Ce qu'il faut noter

Tenez un petit journal, une ligne par épisode. Ce qui m'intéresse, dans cet ordre :

- **Le temps et le nombre d'essais** jusqu'à un `quod_check` vert (l'agent vous le dit, ou lisez la conversation).
- **Les refus** : chaque fois que le compilateur a dit non, *que disait le message*, et *l'agent a-t-il compris tout de suite* ? Copiez les messages qui vous ont paru obscurs.
- **Les contrats** : après l'explication de l'agent, **disent-ils ce que vous vouliez ?** Cherchez surtout ce qu'ils *ne disent pas* (un cas oublié, un arrondi, une limite). Un contrat que vous trouvez juste mais trop faible est exactement ce que le contrôle de complétude doit attraper : notez si c'est le cas.
- **Le C#** (si vous l'essayez) : `quod build programme.quod --target csharp` donne un fichier à ajouter au projet. Se compile-t-il, s'appelle-t-il naturellement ?
- **Ce que vous avez voulu faire et que le langage ne permettait pas** : c'est la liste la plus utile pour décider de la suite.

## Après l'essai

Collez-moi le journal et les messages obscurs. Je classerai : défauts du compilateur (à corriger), messages à rendre plus clairs, trous du langage (à décider), et ce qui était simplement mal expliqué dans le manuel. Si l'essai vous a paru utilisable, c'est aussi ce qu'on pourra écrire sans promesse dans la discussion « First try ».
