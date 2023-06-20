# Historique

## Hashtable avec arbre radix

Pas trop de soucis.

## Hashtable avec tableau et bucket

Qu'est qu'il faut mettre dans les bucket ?

    (clé, valeur) : comparaisone des clé peut être couteux (c1 = c2) (linaire 
        sur la taille de c1)
    
    (hash, clé, valeur) : comparé le hash puis la clé (deux clé différentes
    peuvent avoir le même hache)

    éviter le triplet car ça fait deux boites :

                  +------+---+    +---+---+
    (int, (K, V)) | hash | * | -> | K | V |
                  +------+---+    +---+---+

```
bucket : list (int * K * V)
```

Au début sans invariant et fonction de bases :

- problème avec les preuves :

Il faut des invariants :
    
    1. Tableaux avec taille > 0
    2. Bucket bien formés :
        * Le hash correspond à la valeur (hash k = h)
        * Le tuple est dans le bon bucket

- solution :

   1.  Hypothèse dans les preuves table bien formés et chaque opérations
    nous renvoi une table bien formée (peut rendre les preuves plus difficile
    pour l'utilisateur)
   2.  revoir les fonctions en rajoutant le minium pour retrouver les invariants
    (rajout de tests inutiles si la table de hachage est créé avec l'interface
    données)

#### Resize : 

```
let resize ht =
    let new_ht = create ... in
    for i to 0..len ht - 1 do
        (h, k, v) ... 
        if i = h % len ht then
            ...
    done
```

> la fonction de resize à été très difficile car elle demandait un itérateur sur
> les tableau persistant.

Pour faire ça j'ai utilisé un élément de la théorie de Coq qui s'appelle Acc.
C'est un type qui contient un constructeur _Acc_into_ qui définie une relation
d'accessibilité qui est utilisé ici pour savoir si nous avons dépassé un certain
élément.

#### Fonction de bases

Rajout des fonctions de bases comme remove et replace, preuves très simple
comparé au resize.

##### Itérateur

J'ai commencer à rajouter l'itérateur fold pour les tables de hachage, les
fonctions sont codées. Pour la spec j'ai décider de faire une fonction élément
qui va renvoyer une liste de pair clé valeur.

Comme il n'y a pas de relation d'égalité décidable sur le type des Valeur, 
Guillaume m'a conseiller de faire une relation inductive qui donne le nombre
d'occurrence de la paire clé valeur dans la liste.

```coq
Inductive count {V: T} : list T -> nat -> Prop :=
    | count_nil     : count nil 0
    | count_in      : forall l n, count l n -> count (v :: l) (S n)
    | count_notin   : forall l n w, v <> w -> count (w :: l) n
```

## FMap AVL

J'ai aussi utilisé les FMap de Coq pour comparer l'utilisation (que doit on
faire pour utiliser cette librairie) et aussi pour avoir un aperçut des
différences de performance. Avoir des tests avec des structure de type AVL
(arbre binaire de recherche)

### Utilisation

Déjà pour commencer les FMap sont beaucoup plus difficile à mettre en place.
Il faut faire un module avec:

* une relation équivalence ( = ) avec les théorèmes:
    - eq i i
    - eq n m -> eq m n
    - eq x y -> eq y z -> eq x z
    - reflect (n = m) (eq n m)
* une relation ordre ( < ) avec les théorèmes:
    - x < y -> y < z -> x < z
    - x < y -> x != y
* une fonction compare qui renvoi Eq, Lt ou Gt.
    Avec le théorème OrderedType.Compare lt eq x y.
* Théorème {eq x y} + {~ eq x y}

Après avoir utiliser FMapAVL.Make on a un module avec les fonctions de base des
Maps comme find, add, empty, ...

Cette structure de données est aussi plus lente que les hashtables mais la
performance n'est pas influencé par une potentiel mauvaise fonction de hachage.

## Tests

Il est enfin temps de faire quelque tests pour comparer les performance des
nouvelles tables de hachage.

L'objective est de trouver des fonctions intéressantes pour mémoïser les
résultat. Cela permet de tester l'accès en écriture et en lecture pour les
différents dictionnaires.

### Fibo

Au début j'ai testé sur la fonction de fibonnacci :

```
fibo(0) = 0
fibo(1) = 1
fibo(n + 1) = fibo(n) + fibo (n + 1)
```

Malheureusement cette fonction est linéaire lorsque les calcules sont mémoïsés. 
Le temps n'était pas très représentatif de la performance de la table de
hachage.

### Pascal

L'objectif est de calculer les coefficients binomiaux à l'aide du triangle de
pascal. Cette fois la complexité est quadratique même en mémoïsant.

```
               / 0                                          si 0 < m < n
pascal(n, m) = | 1                                          si n = 0
               \ pascal(n - 1, m - 1) + pascal(n - 1, m)    sinon

     m
    +-----------+
  n | 1         |
    | 1 1       |
    | 1 2 1     |
    | 1 3 3 1   |
    | 1 4 6 4 1 |
    +-----------+
```

| pascal 2n n    | Radix Tree Nat| Bucket Nat| Radix Tree Int | Bucket Int | FMap AVL |
|:------------   | :--------:    | :----:    | :------------: | :--------: | :------: |
| n=50           | 0.093s        | 0.32s     | 0.58s          | 0.02s      | 0.084s   |
| n=100          | 0.331s        | 0.167s    | 0.203s         | 0.026s     | 0.35s    |
| n=150          | 0.919s        | 0.462s    | 0.423s         | 0.092s     | 0.723s   |
| n=200          | 1.917s        | 1.003s    | 0.794s         | 0.114s     | 1.413s   |

Il y des type de fonction de hachage, celle prend des Nat (hn) et celle qui prend 
des Int (hi). La fonction hn est bien plus coûteuse que la fonction hi.

On peut voir qu'avec une fonction de hachage coûteuse comme hn il y a seulement
un facteur 2 de différences en faveur des tables de hachages. Par contre avec
une fonction constante comme hi il y a plus d'un facteur 10 de différences
encore une fois en faveur des tables de hachages.

### Lambda

Échec Total

### Syracuse

Guillaume m'a conseillé de faire plus de tests de performance, on a donc chercher
à faire une fonction qui vérifie la conjecture de Syracuse pour des nombre de 0 à
n.

Voici le pseudo code :

```
h <- []
for i = 1 to +inf
    if (i in h) then h <- h \ {i}
    j <- i
    while true do
        j <- syracuse j
        if j < i then break
        if (j in h) then return 
        h <- h ++ {j}
    done
```

Il y a deux boucles infinie dans ce pseudo code, il faut donc chercher à voir ce
qu'elles vont devenir dans le programme Coq. Guillaume m'a parler de fonction
récursive externe.

Le principe : fonction complètement normal qui serra appelé plusieurs fois par
une autre fonction avec des paramètre en fonction du retour de la fonction
précédente.

TODO: à coder

## Utilisation des théorèmes

Il a fallut tester si les théorèmes donnés était bien suffisant et facile à
utiliser. Pour cela j'ai essayer de faire une preuve sur la fonction du triangle
de pascal mémoïsée.

### Pascal

Pour tester les théorèmes j'ai fait la preuve:

```
    forall n m, pascal_memo (Z.of_nat n) (Z.of_nat m) = pascal n m
```

Pour faire cette preuve Guillaume m'a expliquer la différences entre un
invariant et un invariant inductif.

> Un invariant est une propriété gardée du début à la fin d'une boucle.
> Parfois prouver un invariant peut être impossible donc pour ça on va créé un
> invariant inductif qui rend la preuve de l'invariant trivial et qui peut ce
> prouver par récurrence.

Pour cette preuve on a prouver l'invariant inductif suivant:

```
   forall ht, ok ht -> ok (snd (pascal_memo' n m ht)) 
           /\ fst (pascal_memo' n m ht) = pascal n m
```
avec `ok := forall n' m' i, H.find ht (N n' m') = Some i -> i = pascal n' m'`

pascal_memo appel `pascal_memo' n m ht` avec ht une table de hachage.

Grâce à cet invariant inductif on peut facilement prouver le théorème de base.
Pour prouver l'invariant inductif on va faire une récurrence sur n.

