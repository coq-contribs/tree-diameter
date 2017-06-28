(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* Diameter of a binary tree *)

(* This contribution verifies the following divide-and-conqueer   
    algorithm to compute the diameter of a binary tree (the maximal
    distance between two nodes in the tree).
    The key idea is to compute the height of the tree at the same time.

    let rec diamh = function
     | Empty -> (0, 0)
     | Node (t0, t1) ->
        let (d1, h1) = diamh t0 in
        let (d2, h2) = diamh t1 in
        (max d1 (max d2 (2+h1+h2)), 1+max h1 h2)
*)

Unset Standard Proposition Elimination Names.
Global Set Asymmetric Patterns.

Require Export Omega.
Require Export Arith.
Require Export List.
Require Export Wf_nat.

(* paths in a graph *)

Section Paths.

  Variable A : Set.
  Definition graph := A->A->Prop.
  Variable g : graph.

  (* path x y n = there is a path from x to y of length n *)
  Inductive path : A -> A -> nat -> Prop :=
  | path_nil : forall x, path x x 0 
  | path_cons : forall x1 x2 x3 n, g x1 x2 -> path x2 x3 n ->
                       path x1 x3 (S n).

  (* distance = length of minimal path *)
  Definition dist x y n :=
    path x y n /\ forall m, path x y m -> n <= m.

  Definition diameter n :=
    (exists t1, exists t2, dist t1 t2 n) /\
    (forall t1 t2 m, dist t1 t2 m -> m <= n).

   Lemma path_trans : forall x y z n m, 
     path x y n -> path y z m -> path x z (n+m).
  Proof.
    induction 1; intros.
    replace (0+m) with m; auto with *.
    replace (S n+m) with (S (n+m)); auto with *.
    apply path_cons with x2; auto.   
  Qed.

  Lemma path_1 : forall x y, g x y -> path x y 1.
  Proof.
    intros; apply path_cons with y; auto. apply path_nil.
  Qed.

  Lemma path_snoc : forall x y z n, path x y n -> g y z -> path x z (S n).
  Proof.
    induction 1; intuition.
    apply path_cons with z; auto.
    apply path_nil.
    apply path_cons with x2; auto.
  Qed.

  Lemma path_sym : 
    (forall x y, g x y -> g y x) ->
    forall n x y, path x y n -> path y x n.
  Proof.
    intro g_sym; induction 1.
    apply path_nil.
    apply path_snoc with x2; auto.
  Qed.

End Paths.
Implicit Arguments path [A].
Implicit Arguments dist [A].
Implicit Arguments diameter [A].
Hint Resolve path_sym path_1.
Hint Constructors path.

(* binary trees *)
  
Inductive tree : Set :=
  | Empty : tree
  | Node : tree -> tree -> tree.

(* positions in binary trees *)

Inductive dir : Set := Left : dir | Right : dir.
Definition pos := list dir.

(* validity of a position within a tree *)

Inductive valid : tree -> pos -> Prop := 
  | Vroot : forall t, valid t nil
  | Vleft  : forall l r p, valid l p -> valid (Node l r) (Left :: p)
  | Vright : forall l r p, valid r p -> valid (Node l r) (Right :: p).

Hint Constructors valid.

(* adjacence of two positions *)

Inductive adj : pos -> pos -> Prop :=
  | Aleft1 : adj nil (cons Left nil)
  | Aleft2 : adj (cons Left nil) nil
  | Aright1 : adj nil (cons Right nil)
  | Aright2 : adj (cons Right nil) nil
  | Actx : forall d p1 p2, adj p1 p2 -> adj (d :: p1) (d :: p2).

Hint Constructors adj.

Lemma adj_sym : forall p1 p2, adj p1 p2 -> adj p2 p1.
Proof.
  induction 1; auto.
Qed.
Hint Resolve adj_sym.

(* the graph induced by a binary tree *)

Definition gt (t:tree) (p1 p2 : pos) : Prop :=
  valid t p1 /\ valid t p2 /\ adj p1 p2.

Lemma gt_sym : forall t p1 p2, gt t p1 p2 -> gt t p2 p1.
Proof.
  unfold gt; intuition.
Qed.
Hint Resolve gt_sym.

Lemma gt_empty : forall t1 t2, ~(gt Empty t1 t2).
Proof.
  red; intros.
  inversion_clear H; intuition.
  inversion H0; subst.
  inversion H; subst.
  inversion_clear H2.
Qed.

Lemma path_gt_r: forall l r p1 p2 n,
  path (gt r) p1 p2 n -> path (gt (Node l r)) (Right::p1) (Right::p2) n.
Proof.
  induction 1; auto.
  apply path_cons with (Right::x2); auto.
  red in H; red; intuition.
Qed.

Lemma path_gt_l: forall l r p1 p2 n,
  path (gt l) p1 p2 n -> path (gt (Node l r)) (Left::p1) (Left::p2) n.
Proof.
  induction 1; auto.
  apply path_cons with (Left::x2); auto.
  red in H; red; intuition.
Qed.

Lemma path_gt_r_root_inv : forall l r n,
  (forall p2, path (gt (Node l r)) nil (Right::p2) n -> 
     exists n', n' < n /\ path (gt r) nil p2 n') /\
  (forall p2, path (gt (Node l r)) nil (Left::p2) n -> 
     exists n', n' < n /\ path (gt l) nil p2 n') /\
  (forall p1 p2,
    path (gt (Node l r)) (Right::p1) (Right::p2) n -> 
    exists n', n'<=n /\ path (gt r) p1 p2 n') /\
  (forall p1 p2,
    path (gt (Node l r)) (Left::p1) (Left::p2) n -> 
    exists n', n'<=n /\ path (gt l) p1 p2 n') /\
  (forall p1 p2,
   path (gt (Node l r)) (Left::p1) (Right::p2) n ->
   exists m1, exists m2,
     path (gt l) p1 nil m1 /\ path (gt r) nil p2 m2 /\ n>=2+m1+m2).
Proof.
  intros l r n; pattern n; apply (well_founded_ind lt_wf).
  clear n; intros n Hn; intuition.
  (* root Right *)
  inversion H; subst.
  destruct x2.
  inversion H0; intuition.
  inversion H5.
  destruct d.
  elim (Hn n0); intuition.
  elim (H7 _ _ H1); intros m1 (m2,(h1,(h2,h3))).
  exists m2; intuition.
  elim (Hn n0); intuition.
  elim (H3 x2 p2); intuition.
  exists x; intuition.
  inversion H0; intuition.
  inversion H12.
  rewrite H10; auto.
  (* root Left *)
  inversion H; subst.
  destruct x2.
  inversion H0; intuition.
  inversion H5.
  destruct d.
  elim (Hn n0); intuition.
  elim (H5 x2 p2); intuition.
  exists x; intuition.
  inversion H0; intuition.
  inversion H12.
  rewrite H10; auto.
  elim (Hn n0); intuition.
  assert (path (gt (Node l r)) (Left :: p2) (Right :: x2) n0).
  apply path_sym; auto.
  elim (H7 _ _ H6); intros m1 (m2,(h1,(h2,h3))).
  exists m1; intuition.
  (* inv Right *)
  inversion H; subst.
  exists 0; auto.
  destruct x2.
  elim (Hn n0); intuition; clear H4 H5 H7.
  elim (H2 p2); intuition.
  exists x; intuition.
  inversion H0; intuition.
  inversion H9; subst; auto.
  destruct d.
  red in H0; intuition.
  inversion H4.
  elim (Hn n0); intuition; clear H4 H5 H7.
  elim (H3 x2 p2); auto.
  intros n' (h1,h2).
  exists (S n'); intuition.
  apply path_cons with x2; auto.
  red; red in H0; intuition.
  inversion H4; auto.
  inversion H0; auto.
  inversion H6; auto.
  (* inv Left *)
  inversion H; subst.
  exists 0; auto.
  destruct x2.
  elim (Hn n0); intuition; clear H2 H3 H7.
  elim (H4 p2); intuition.
  exists x; intuition.
  inversion H0; intuition.
  inversion H9; subst; auto.
  destruct d.
  elim (Hn n0); intuition; clear H2 H3 H7.
  elim (H5 x2 p2); auto.
  intros n' (h1,h2).
  exists (S n'); intuition.
  apply path_cons with x2; auto.
  red; red in H0; intuition.
  inversion H2; auto.
  inversion H0; auto.
  inversion H6; auto.
  red in H0; intuition.
  inversion H4.
  (* split *)
  inversion H; subst.
  destruct x2; intuition.
  exists 0.
  elim (Hn n0); intuition.
  elim (H2 _ H1); intuition.
  exists x; intuition.
  red in H0; intuition.
  inversion H11; subst; auto.
  destruct d.
  elim (Hn n0); intuition.
  elim (H7 _ _ H1); intros m1 (m2,(h1,(h2,h3))).
  assert (path (gt (Node l r)) (Left :: p1) (Left :: x2) 1).
  apply path_1; auto.
  elim (Hn 1); intuition.
  elim (H11 _ _ H6); clear H8 H10 H9 H11 H13.
  intros m' (hm'1,hm'2).
  exists (m'+m1); exists m2; intuition.
  apply path_trans with x2; auto.
  red in H0; intuition.
  inversion H4.
Qed.

Lemma path_gt_r_root : forall l r n p2,
  path (gt (Node l r)) nil (Right::p2) n -> 
  exists n', n' < n /\ path (gt r) nil p2 n'.
Proof.
  intros l r n; generalize (path_gt_r_root_inv l r n); intuition.
Qed.

Lemma path_gt_r_inv : forall l r n p1 p2,
  path (gt (Node l r)) (Right::p1) (Right::p2) n -> 
  exists n', n'<=n /\ path (gt r) p1 p2 n'.
Proof.
  intros l r n; generalize (path_gt_r_root_inv l r n); intuition.
Qed.

Lemma split : forall l r m p1 p2,
   path (gt (Node l r)) (Left::p1) (Right::p2) m ->
   exists m1, exists m2,
     path (gt l) p1 nil m1 /\ path (gt r) nil p2 m2 /\ m>=2+m1+m2.
Proof.
  intros l r m; generalize (path_gt_r_root_inv l r m); intuition.
Qed.

Lemma path_gt_l_root : forall l r n p2,
  path (gt (Node l r)) nil (Left::p2) n -> 
  exists n', n' < n /\ path (gt l) nil p2 n'.
Proof.
  intros l r n; generalize (path_gt_r_root_inv l r n); intuition.
Qed.

Lemma path_gt_l_inv : forall l r n p1 p2,
  path (gt (Node l r)) (Left::p1) (Left::p2) n -> 
  exists n', n'<=n /\ path (gt l) p1 p2 n'.
Proof.
  intros l r n; generalize (path_gt_r_root_inv l r n); intuition.
Qed.

Require Export Max.

Fixpoint height (t:tree) : nat := match t with
  | Empty => 0
  | Node l r => S (max (height l) (height r))
end.

Ltac Max n m := 
  cut (m <= n \/ n <= m);
  [ intros [h|h]; [ rewrite max_l | rewrite max_r ]
  | omega ].

Lemma max_1 : forall n m, n<=m -> max n m = m.
Proof. intros n m; Max n m; intuition. Qed.

Lemma max_2 : forall n m p, n <= m -> n <= max m p.
Proof. intros n m p; Max m p; intuition. Qed.

Lemma max_3 : forall n m, n>m -> max n m = n.
Proof. intros n m; Max n m; intuition. Qed.

Lemma max_4 : forall n m p, n <= p -> n <= max m p.
Proof. intros n m p; Max m p; intuition. Qed.

Lemma max_5 : forall n m, n <= max n m.
Proof. intros n m; Max n m; intuition. Qed.

Lemma max_6 : forall n m, m <= max n m.
Proof. intros n m; Max n m; intuition. Qed.

Lemma max_7 : forall n m, max n m <= n+m.
Proof. intros n m; Max n m; intuition. Qed.

Lemma max_3_cases : forall x y z,
  (x >= y /\ x >= z /\ max x (max y z) = x) \/
  (y >= x /\ y >= z /\ max x (max y z) = y) \/
  (z >= x /\ z >= y /\ max x (max y z) = z).
Proof.
  intros x y z.
  assert (y<=z \/ y>=z). omega. intuition.
  replace (max y z) with z.
  Max x z; intuition.
  rewrite max_r; intuition.
  replace (max y z) with y.
  Max x y; intuition.
  rewrite max_l; intuition.
Qed.

Hint Resolve max_2.

Lemma dist_height : forall t, exists p, dist (gt t) nil p (height t).
Proof.
  induction t; simpl.
  unfold dist; exists (@nil dir); intuition.
  case (le_gt_dec (height t1) (height t2)); intro.
  (* height t1 <= height t2 *)
  rewrite max_1; auto.
  clear IHt1; elim IHt2; intros p2; clear IHt2; exists (Right :: p2).
  red; intuition.
  apply path_cons with (cons Right nil); auto.
  red; red in H; intuition.
  red in H; intuition.
  apply path_gt_r; auto.
  red in H; intuition.
  elim (path_gt_r_root _ _ _ _ H0); intros x (Hm1, Hm2).
  generalize (H2 _ Hm2).
  omega.
  (* height t1 > height t2 *)
  rewrite max_3; auto.
  clear IHt2; elim IHt1; intros p1; clear IHt1; exists (Left :: p1).
  red; intuition.
  apply path_cons with (cons Left nil); auto.
  red; red in H; intuition.
  red in H; intuition.
  apply path_gt_l; auto.
  red in H; intuition.
  elim (path_gt_l_root _ _ _ _ H0); intros x (Hm1, Hm2).
  generalize (H2 _ Hm2).
  omega.
Qed.

Lemma dist_height_max :
  forall t p n, dist (gt t) nil p n -> n <= height t.
Proof.
  induction t; simpl.
  unfold dist; intuition.
  inversion H0; subst; auto.
  elim (gt_empty _ _ H).
  unfold dist; destruct p; simpl; intuition.
  inversion H0; subst.
  generalize (H1 0 H0); auto with *.
  assert (S n0 <= 0).
  apply H1; auto.
  omega.
  destruct d.
  elim (path_gt_l_root _ _ _ _ H0); intros x (hx1,hx2).
  apply le_trans with (1+height t1).
  assert (x<n-1 \/ x=n-1). omega. intuition.
  assert (n<=S x).
  apply H1.
  apply path_cons with (cons Left nil).
  unfold gt; auto.
  apply path_gt_l; auto.
  omega.
  assert (x<=height t1).
  apply IHt1 with p; red; intuition.
  assert (n<=S m).
  apply H1.
  apply path_cons with (cons Left nil).
  unfold gt; auto.
  apply path_gt_l; auto.
  omega.
  omega.
  generalize (max_5 (height t1) (height t2)); omega.
  (* Right *)
  elim (path_gt_r_root _ _ _ _ H0); intros x (hx1,hx2).
  apply le_trans with (1+height t2).
  assert (x<n-1 \/ x=n-1). omega. intuition.
  assert (n<=S x).
  apply H1.
  apply path_cons with (cons Right nil).
  unfold gt; auto.
  apply path_gt_r; auto.
  omega.
  assert (x<=height t2).
  apply IHt2 with p; red; intuition.
  assert (n<=S m).
  apply H1.
  apply path_cons with (cons Right nil).
  unfold gt; auto.
  apply path_gt_r; auto.
  omega.
  omega.
  generalize (max_6 (height t1) (height t2)); omega.
Qed.

(* diameter of a binary tree *)

Definition Diameter t := diameter (gt t).

Lemma key_lemma : forall t1 t2 d1 d2,
  Diameter t1 d1 -> Diameter t2 d2 ->
  Diameter (Node t1 t2) (max d1 (max d2 (2+height t1+height t2))).
Proof.
  unfold Diameter.
  intros t1 t2 d1 d2 ((t11, (t12, h1t1)),h2t1).
  intros ((t21,(t22,h1t2)),h2t2).
  split.
  elim (max_3_cases d1 d2 (2+height t1+height t2)).
  intros (hmax1,(hmax2 ,hmax3)); rewrite hmax3; clear hmax3.
  (* d1 >= d2, 2+h t1+h t2 *)
  exists (Left::t11); exists (Left::t12); red; intuition.
  apply path_gt_l.
  red in h1t1; intuition.
  red in h1t1; intuition.
  elim (path_gt_l_inv _ _ _ _ _ H); intros m' (h1,h2).
  apply le_trans with m'; auto.
  intros [(hmax1,(hmax2,hmax3)) | (hmax1,(hmax2,hmax3))];
  rewrite hmax3; clear hmax3.
  (* d2 >= d1, 2+h t1+h t2 *)
  exists (Right::t21); exists (Right::t22); red; intuition.
  apply path_gt_r.
  red in h1t2; intuition.
  red in h1t2; intuition.
  elim (path_gt_r_inv _ _ _ _ _ H); intros m' (h1,h2).
  apply le_trans with m'; auto.
  (* d1, d2 <= 2+height t1+height t2 *)
  elim (dist_height t1); intros p1 hp1.
  elim (dist_height t2); intros p2 hp2.
  exists (Left::p1); exists (Right::p2); red; intuition.
  red in hp1; red in hp2; intuition.
  replace (2+height t1+height t2) with (height t1+(1+(1+(height t2)))); auto with *.
  apply path_trans with (Left::nil).
  apply path_gt_l; auto.
  apply path_trans with (@nil dir); auto.
  apply path_1; red; auto.
  apply path_trans with (Right::nil); auto.
  apply path_1; red; auto.
  apply path_gt_r; auto.
  elim (split _ _ _ _ _ H); intros m1 (m2, (h1,(h2,h3))).
  red in hp1; red in hp2; intuition.
  assert (path (gt t1) nil p1 m1); auto.
  generalize (H1 m1 H4).
  generalize (H3 m2 h2).
  omega.
  (* every distance in (Node t1 t2) is smaller than max d1 ... *)
  unfold dist; intuition.
  destruct t0; destruct t3.
  (* nil - nil *)
  assert (path (gt (Node t1 t2)) nil nil 0); auto.
  generalize (H1 0 H); omega.
  (* nil - d::t3 *)
  destruct d.
  do 2 apply max_4.
  apply le_trans with (height (Node t1 t2)).
  apply dist_height_max with (Left::t3); red; intuition.
  simpl.
  generalize (max_7 (height t1) (height t2)); omega.
  do 2 apply max_4.
  apply le_trans with (height (Node t1 t2)).
  apply dist_height_max with (Right::t3); red; intuition.
  simpl.
  generalize (max_7 (height t1) (height t2)); omega.
  (* d::t0 - nil *)
  destruct d.
  do 2 apply max_4.
  apply le_trans with (height (Node t1 t2)).
  apply dist_height_max with (Left::t0); red; intuition.
  simpl.
  generalize (max_7 (height t1) (height t2)); omega.
  do 2 apply max_4.
  apply le_trans with (height (Node t1 t2)).
  apply dist_height_max with (Right::t0); red; intuition.
  simpl.
  generalize (max_7 (height t1) (height t2)); omega.
  (* d::t0 - d0::t3 *)
  destruct d; destruct d0; simpl.
  (* Left::t0 - Left::t3 *)
  apply max_2.
  elim (path_gt_l_inv _ _ _ _ _ H0); intros m' (hm'1,hm'2).
  assert (m<=m').
  apply H1; apply path_gt_l; auto.
  assert (dist (gt t1) t0 t3 m').
  red; intuition.
  replace m' with m; [idtac|omega].
  apply H1; apply path_gt_l; auto.
  replace m with m'; [idtac|omega].
  apply (h2t1 _ _ _ H2).
  (* Left::t0 - Right::t3 *)
  do 2 apply max_4.
  elim (split _ _ _ _ _ H0); intros m1 (m2, (h1,(h2,h3))).
  assert (m <= m1+S(S m2)).
  apply H1.
  apply path_trans with (Left::nil); auto.
  apply path_gt_l; auto.
  apply path_cons with (@nil dir); auto.
  red; intuition.
  apply path_cons with (Right::nil); auto.
  red; intuition.
  apply path_gt_r; auto.
  assert (m1 <= height t1).
  apply dist_height_max with t0.
  red; intuition.
  assert (m1 <= m0 \/ m1 > m0). omega. intuition.
  assert (path (gt (Node t1 t2)) (Left::t0) (Right::t3) (m0+S(S m2))).
  apply path_trans with (Left::nil); auto.
  apply path_gt_l; auto.
  apply path_cons with (@nil dir); auto.
  red; intuition.
  apply path_cons with (Right::nil); auto.
  red; intuition.
  apply path_gt_r; auto.
  generalize (H1 _ H3); omega.
  assert (m2 <= height t2).
  apply dist_height_max with t3.
  red; intuition.
  assert (m2 <= m0 \/ m2 > m0). omega. intuition.
  assert (path (gt (Node t1 t2)) (Left::t0) (Right::t3) (m1+S(S m0))).
  apply path_trans with (Left::nil); auto.
  apply path_gt_l; auto.
  apply path_cons with (@nil dir); auto.
  red; intuition.
  apply path_cons with (Right::nil); auto.
  red; intuition.
  apply path_gt_r; auto.
  generalize (H1 _ H4); omega.
  omega.
  (* Right::t0 - Left::t3 *)
  do 2 apply max_4.
  assert (path (gt (Node t1 t2)) (Left::t3) (Right::t0) m); auto.
  elim (split _ _ _ _ _ H); intros m1 (m2, (h1,(h2,h3))).
  assert (m <= m2+S(S m1)).
  apply H1.
  apply path_trans with (Right::nil); auto.
  apply path_gt_r; auto.
  apply path_cons with (@nil dir); auto.
  red; intuition.
  apply path_cons with (Left::nil); auto.
  red; intuition.
  apply path_gt_l; auto.
  assert (m1 <= height t1).
  apply dist_height_max with t3.
  red; intuition.
  assert (m1 <= m0 \/ m1 > m0). omega. intuition.
  assert (path (gt (Node t1 t2)) (Right::t0) (Left::t3) (m2+S(S m0))).
  apply path_trans with (Right::nil); auto.
  apply path_gt_r; auto.
  apply path_cons with (@nil dir); auto.
  red; intuition.
  apply path_cons with (Left::nil); auto.
  red; intuition.
  apply path_gt_l; auto.
  generalize (H1 _ H4); omega.
  assert (m2 <= height t2).
  apply dist_height_max with t0.
  red; intuition.
  assert (m2 <= m0 \/ m2 > m0). omega. intuition.
  assert (path (gt (Node t1 t2)) (Right::t0) (Left::t3) (m0+S(S m1))).
  apply path_trans with (Right::nil); auto.
  apply path_gt_r; auto.
  apply path_cons with (@nil dir); auto.
  red; intuition.
  apply path_cons with (Left::nil); auto.
  red; intuition.
  apply path_gt_l; auto.
  generalize (H1 _ H5); omega.
  omega.
  (* Right::t0 - Right::t3 *)
  apply max_4; apply max_2.
  elim (path_gt_r_inv _ _ _ _ _ H0); intros m' (hm'1,hm'2).
  assert (m<=m').
  apply H1; apply path_gt_r; auto.
  assert (dist (gt t2) t0 t3 m').
  red; intuition.
  replace m' with m; [idtac|omega].
  apply H1; apply path_gt_r; auto.
  replace m with m'; [idtac|omega].
  apply (h2t2 _ _ _ H2).
Qed.

Definition diamh (t:tree) : 
  { r:nat*nat | let (d,h) := r in Diameter t d /\ h=height t }.
Proof.
  induction t; simpl.
  (* t = Empty *)
  exists (0,0); intuition.
  split.
  exists (@nil dir); exists (@nil dir); red; intuition; auto.
  intros.
  inversion H.
  inversion_clear H0; auto.
  elim (gt_empty _ _ H2).
  (* t = Node t1 t2 *)
  elim IHt1; intros (d1, h1); clear IHt1.
  elim IHt2; intros (d2, h2); clear IHt2.
  intuition.
  exists (max d1 (max d2 (2+h1+h2)), 1+max h1 h2); split.
  subst; apply key_lemma; auto.  
  subst; auto.
Defined.

Definition diam (t:tree) : { d:nat | Diameter t d }.
Proof.
  refine (match diamh t with
          | exist dh _ => (exist _ (fst dh) _)
          end).
  destruct dh; simpl; intuition.
Defined.


