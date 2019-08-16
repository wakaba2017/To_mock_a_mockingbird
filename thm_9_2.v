Require Import String.
Open Scope string_scope.

Inductive bird : Set :=
  | app : bird -> bird -> bird.

Module thm_9_2.

  Variable M : bird. (* ものまね鳥を示す変数 *)
  Variable E : bird. (* ものまね鳥が好きな鳥を示す変数 *)

  (*
    合成鳥の存在を示すのと同値な仮定
    (鳥の合成ルールを示す仮定)
  *)
  Hypothesis Hc : forall (A B x : bird), app A (app B x) = app (app A B) x.

  (* ものまね鳥の性質を示す仮定 *)
  Hypothesis Hm : forall (x : bird), app M x = app x x.

  (* ものまね鳥が好きな鳥を示す仮定 *)
  Hypothesis He : app M E = E. (* ← app M E が、ものまね鳥の性質により、app E E と書けることがカギ *)

  Theorem thm_9_2 :
    exists (x : bird), app x x = x.
      (*
        結論：
        ある x が存在して、 x x = x となる。
      *)
  Proof.
    exists E.
    rewrite <- He at 3.
    rewrite Hm.
    reflexivity.
  Qed.

  From mathcomp
  Require Import ssreflect.

  Theorem thm_9_2_ssr :
    exists (x : bird), app x x = x.
      (*
        結論：
        ある x が存在して、 x x = x となる。
      *)
  Proof.
    exists E.
    rewrite -{3} He. (* rewrite <- He at 3.と同じこと。 *)
    rewrite Hm.
    done.
  Qed.

End thm_9_2.
