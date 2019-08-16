Inductive bird : Set :=
  | app : bird -> bird -> bird.

Module thm_9_3.

  Variable A : bird. (* 同調鳥を示す変数 *)

  (*
    合成鳥の存在を示すのと同値な仮定
    (鳥の合成ルールを示す仮定)
  *)
  Hypothesis Hc : forall (A B x : bird), app A (app B x) = app (app A B) x.

  (* 同調鳥の性質を示す仮定 *)
  Hypothesis Ha : forall (B : bird), (exists (x' : bird), app A x' = app B x').
  Hypothesis Ha' : forall (x : bird), (exists (x' : bird), app A x' = app (app x A) x').
  (*
    Coqの証明で、HaからHa'を導く手順が思い浮かばなかったため、
    今回は手動でHa'を作成し、Ha'を使った照明。
  *)

  Theorem thm_9_3 :
    forall (P : bird),
      exists (x : bird), app P x = x.
    (*
      結論：
      任意の P について、ある x が存在して、 P x = x となる。
    *)
  Proof.
    intros P.
    destruct Ha' with (x := P) as [x' Ha''].
    exists (app A x').
    rewrite Hc with (A := P) (B := A) (x := x').
    rewrite Ha''.
    reflexivity.
  Qed.

  From mathcomp
  Require Import ssreflect.

  Theorem thm_9_3_ssr :
    forall (P : bird),
      exists (x : bird), app P x = x.
  Proof.
    move=> P.
    case Ha' with (x := P) => [x' Ha''].
    exists (app A x').
    rewrite Hc.
    rewrite Ha''.
    done.
  Qed.

End thm_9_3.
