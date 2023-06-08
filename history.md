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
        * Le hash corespond à la valeur (hash k = h)
        * Le tuple est dans le bon bucket

- solution :

1.  Hypothèse dans les preuves table bien formés et chaques opérations
    nous renvoi une table bien formée (peut rendre les preuves plus difficle
    pour l'utilisateur)
2.  revoir les fonctions en rajoutant le minium pour retrouver les invariants
    (rajout de tests inutiles si la table de hachage est créé avec l'interface
    données)

    Resize : 

```
let resize ht =
    let new_ht = create ... in
    for i to 0..len ht - 1 do
        (h, k, v) ... 
        if i = h % len ht then
            ...
    done
```

Resize:

> la fonction de resize à été très difficle car elle demandait un itérateur sur
> les tableau persistant.

Pour faire ça j'ai utilisé un élément de la théorie de Coq qui s'appel Acc.
C'est un type qui contient un constructeur _Acc_into_ qui définie une relation
d'accésibilité qui est utilisé ici pour savoir si nous avons dépassé un certaint
élement.

rajout des fonctions de bases comme remove et replace, preuves très simple
comparé au resize.

## Tests

Il est enfi temps de faire queqlue tests pour comparer les performance des
nouvelles tables de hachage.

L'objective est de trouver des fonctions interssantes pour mémoïser les
résultat. Cela permet de tester l'accès en écriture et en lecture pour les
différents dictionnaires.

### Fibo

Au début j'ai testé sur la fonction de fibonnacci:

```
fibo(0) = 0
fibo(1) = 1
fibo(n + 1) = fibo(n) + fibo (n + 1)
```

Malheuresement cette fonction est linéaire lorsque les calcules sont mémoïsés. Le temps n'était pas très représentatif de la performance de la table de
hachage.

### Pascal

L'objectif est de calculer les coefficients binomiaux à l'aide du triangle de
pascal. Cette foit la complexité est quadratique même en mémoïsant.

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

| pascal 2n n    | Radix Tree Nat| Bucket Nat| Radix Tree Int | Bucket Int |
|:------------   | :--------:    | :----:    | :------------: | :--------: |
| n=50           | 0.093s        | 0.32s     | 0.58s          | 0.02s      |
| n=100          | 0.331s        | 0.167s    | 0.203s         | 0.026s     |
| n=150          | 0.919s        | 0.462s    | 0.423s         | 0.092s     |
| n=200          | 1.917s        | 1.003s    | 0.794s         | 0.114s     |

Il y des type de fonction de hachage, celle prend des Nat (hn) et celle qui prend 
des Int (hi). La fonction hn est bien plus coûteuse que la fonction hi.

On peut voir qu'avec une fonction de hachage coûteuse comme hn il y a seuelement
un facteur 2 de différences en faveur des tables de hachages. Par contre avec
une fonction constante comme hi il y a plus d'un facteur 10 de différences
encore une fois en faver des tables de hachages.

### Lambda

Échec Total
