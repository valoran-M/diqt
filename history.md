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
    nous renvoi une table bien formée
2.  revoir les fonctions en rajoutant le minium pour retrouver les invariants

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
