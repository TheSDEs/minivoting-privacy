require import List Int Option FSet.
require import OldMonoid.

(* length of resulting list is equal to min(xs,ys) *)
op zip (xs: 'a list) (ys : 'b list) =
   with xs = [],    ys = []    => []
   with xs = x::xs, ys = y::ys => (x,y)::(zip xs ys)
   with xs = x::xs, ys = []    => []
   with xs = [],    ys = y::ys => [].


lemma nth_eq_eq (xs ys : 'a list):
  size xs = size ys =>
  (forall (j : int),
     0 <= j < size xs => oget (onth xs j) = oget (onth ys j)) =>
  xs = ys.
proof. 
  move: ys.
  elim xs.
  + smt.
  + progress. 
    move: H1 H0. 
    case ys.
    + smt.
    + progress; expect 2. 
      + cut := H0 0 _; smt. 
      + cut := H l0 _ _.
        + smt.
        + progress; cut := H0 (j + 1) _; smt. 
        by smt.
qed.

lemma Mrplus_inter_shift (i j k:int) f: 
  Mrplus.sum f (oflist (List.Iota.iota_ i (j-i+1))) = 
  Mrplus.sum (fun l, f (l + k)) (oflist (List.Iota.iota_ (i-k) (j-i+1))).
proof.
  rewrite (Mrplus.sum_chind f (fun l, l - k) (fun l, l + k)) /=;first smt.
  congr => //.   
  apply FSet.fsetP => x.
  rewrite imageP !mem_oflist !List.Iota.mem_iota; split.
    move => [y].
    rewrite !mem_oflist !List.Iota.mem_iota.
    progress; smt. 
  move=> Hx;exists (x+k);rewrite !mem_oflist !List.Iota.mem_iota;smt.
qed.

(* lemma take_onth, based on take_nth *)
lemma take_onth n (s: 'a list): 0<= n< size s =>
   take (n + 1) s  = rcons (take n s) (oget (onth s n)).
proof.
   move => H.
   have H1: forall z, take (n + 1) s = 
                      rcons (take n s) (nth z s n) by smt.         
   have H2: forall z, rcons (take n s) (nth z s n) = 
                      rcons (take n s) (oget (onth s n)) by smt.
   by smt.
qed.

lemma onth_rcons (xs: 'a list) x n:
  0 <= n < size (xs ++[x]) =>
  oget( onth (xs ++ [x]) n) = if n = size xs then x
                              else (oget (onth xs n)).
proof.
  move=> H; smt.
qed.

lemma onth_append_left (ys xs: 'a list) n:
  0<= n < size xs =>
  oget( onth (xs ++ys) n) = oget( onth xs n).
proof.
  elim xs =>//=. smt. progress. 
  case (n = 0). smt. 
  move => H2. 
  have Hx: 0 <= (n-1) < size l.
    have support1: 0 <= n-1 by smt.
    have support2: n-1 < size l by smt.
    smt.
  smt.
qed.

lemma onth_append_right (ys xs: 'a list) n:
  size xs <= n < size xs + size ys =>
  oget( onth (xs ++ys) n) = oget( onth ys (n- size xs)).
proof.
  move: n. 
  elim xs =>//=. 
  progress. 
  have ->: (n=0) = false.
    have Hx: 0 <= size l by smt. 
    rewrite lez_add1r in H0.
    smt.
  progress. 
  have Hx: size l <= (n-1) < size l + size ys by smt. 
  rewrite (H (n-1) Hx).
  by smt.
qed.
