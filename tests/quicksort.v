Require Import Coq.Numbers.Cyclic.Int63.Uint63.

Inductive term :=
  | Ref : int -> term
  | Abs : term -> term
  | App : term -> term -> term.

Definition quicksort := App (App (Abs (Abs (App (Ref 0) (App (App (Ref 1) (Ref 1)) (Ref 0)))))
     (Abs (Abs (App (Ref 0) (App (App (Ref 1) (Ref 1)) (Ref 0))))))
(Abs
 (App (Abs (Abs (App (App (Ref 0) (Ref 1)) (Abs (Abs (Ref 0))))))
  (Abs
   (Abs
    (App (Abs
          (App (App (Abs
                     (Abs
                      (Abs
                       (Abs
                        (App (App (Ref 3) (Ref 1))
                         (App (App (Ref 2) (Ref 1)) (Ref 0)))))))
                (App (Ref 3)
                 (App (Abs (App (Ref 0) (Abs (Abs (Ref 1))))) (Ref 0))))
           (App (App (Abs
                      (Abs
                       (Abs
                        (Abs
                         (App (App (Ref 1) (Ref 3))
                          (App (App (Ref 2) (Ref 1)) (Ref 0)))))))
                 (Ref 2))
            (App (Ref 3)
             (App (Abs (App (Ref 0) (Abs (Abs (Ref 0))))) (Ref 0))))))
     (App (App (Abs
                (Abs
                 (App (Abs
                       (App (App (Ref 1) (Ref 0))
                        (App (App (Abs
                                   (Abs
                                    (Abs (App (App (Ref 0) (Ref 2)) (Ref 1)))))
                              (Abs (Abs (Ref 0))))
                         (Abs (Abs (Ref 0))))))
                  (Abs
                   (Abs
                    (App (Abs
                          (App (Abs
                                (App (App (App (Ref 5) (Ref 3))
                                      (App (App (Abs
                                                 (Abs
                                                  (Abs
                                                   (App (App (Ref 0) (Ref 2))
                                                    (Ref 1)))))
                                            (App (App (Abs
                                                       (Abs
                                                        (Abs
                                                         (Abs
                                                          (App (App (
                                                                Ref 1)
                                                                (Ref 3))
                                                           (App (App (
                                                                 Ref 2)
                                                                 (Ref 1))
                                                            (Ref 0)))))))
                                                  (Ref 3))
                                             (Ref 1)))
                                       (Ref 0)))
                                 (App (App (Abs
                                            (Abs
                                             (Abs
                                              (App (App (Ref 0) (Ref 2))
                                               (Ref 1)))))
                                       (Ref 1))
                                  (App (App (Abs
                                             (Abs
                                              (Abs
                                               (Abs
                                                (App (App (Ref 1) (Ref 3))
                                                 (App (App (Ref 2) (Ref 1))
                                                  (Ref 0)))))))
                                        (Ref 3))
                                   (Ref 0)))))
                           (App (Abs (App (Ref 0) (Abs (Abs (Ref 0)))))
                            (Ref 1))))
                     (App (Abs (App (Ref 0) (Abs (Abs (Ref 1))))) (Ref 0))))))))
           (App (Abs
                 (Abs
                  (App (App (App (App (Ref 1)
                                  (App (Abs
                                        (Abs
                                         (App (Abs
                                               (App (Ref 0)
                                                (Abs (Abs (Ref 0)))))
                                          (App (App (Ref 0) (Ref 1))
                                           (App (App (Abs
                                                      (Abs
                                                       (Abs
                                                        (App (App (Ref 0)
                                                              (Ref 2))
                                                         (Ref 1)))))
                                                 (Abs (Abs (Ref 0))))
                                            (Abs (Abs (Ref 0))))))))
                                   (Abs
                                    (App (Abs
                                          (App (App (Abs
                                                     (Abs
                                                      (Abs
                                                       (App (App (Ref 0)
                                                             (Ref 2))
                                                        (Ref 1)))))
                                                (App (Abs
                                                      (Abs
                                                       (Abs
                                                        (App (Ref 1)
                                                         (App (App (Ref 2)
                                                               (Ref 1))
                                                          (Ref 0))))))
                                                 (Ref 0)))
                                           (Ref 0)))
                                     (App (Abs
                                           (App (Ref 0) (Abs (Abs (Ref 1)))))
                                      (Ref 0))))))
                             (Ref 0))
                        (App (Abs (Abs (Ref 1))) (Abs (Abs (Ref 0)))))
                   (Abs (Abs (Ref 1))))))
            (Ref 1)))
      (Ref 0))))))).

