Inductive bird : Set :=
  | app : bird -> bird -> bird.

Theorem thm1 :

  (forall (A B : bird),
    exists (C : bird), forall (x : bird), app A (app B x) = app C x) ->
    (*
      仮定：Hc
      任意の A, B について、ある C が存在して、任意の x に対して A (B x) = C x となる。
    *)

  (exists (M : bird), forall (x : bird), app M x = app x x) ->
    (*
      仮定：Hm
      ある M が存在して、任意の x に対して、 M x = x x となる。
    *)

  (forall (P : bird),
    exists (x : bird), app P x = x).
    (*
      結論：
      任意の P について、ある x が存在して、 P x = x となる。
    *)

Proof.
  intros Hc Hm P.
  destruct Hm as [M Hm'].
  destruct Hc with (A := P) (B := M) as [x' Hc'].
  exists (app M x').
  rewrite Hc'.
  rewrite Hm'.
  reflexivity.
Qed.

(*
  以下はMathcompを使って証明してみた例
*)

From mathcomp
Require Import ssreflect.

Theorem thm1_ssr :
  (forall (A B : bird),
    exists (C : bird), forall (x : bird), app A (app B x) = app C x) ->
  (exists (M : bird), forall (x : bird), app M x = app x x) ->
  (forall (P : bird),
    exists (x : bird), app P x = x).
Proof.
  move=> Hc Hm P.

(*
須原さんからの指摘箇所を修正
  case Hm as [M Hm'].
*)
  case: Hm.
  move=> M Hm'.
  (* 慣れたら、一行で書くこと！ *)

(*
須原さんからの指摘箇所を修正
  case Hc with (A := P) (B := M) as [x' Hc'].
*)
  case (Hc P M). (* カッコがないとエラーとなる模様 *)
  move=> PM Hc'. (* PM:birdが、P:bird,M:birdの合成であることが一目瞭然 *)
  (* 慣れたら、一行で書くこと！ *)

(*
須原さんからの指摘箇所を修正
  exists (app M x').
*)
  exists (app M PM).

  rewrite Hc'.
  rewrite Hm'.
  by [].
Qed.

Theorem thm1_ssr' : (* 須原さんの証明　※自分のスクリプトを手直ししてくれた版 *)
  (forall (A B : bird),
    exists (C : bird), forall (x : bird), app A (app B x) = app C x) ->
  (exists (M : bird), forall (x : bird), app M x = app x x) ->
  (forall (P : bird),
    exists (x : bird), app P x = x).
Proof.
  move=> Hc Hm P.
  case: Hm => [M Hm'].      (* Hm' は ものまね鳥 M についての命題。 *)
  case: (Hc P M) => [PM Hc']. (* Hc' は P と M を合成した、合成鳥PMについての命題。 *)
  exists (app M PM).
  rewrite Hc'.            (* 左辺のP と Mから合成鳥PMを得る。 *)
  rewrite Hm'.            (* 右辺のM PM からものまね鳥 M M を得る。 *)
  by [].
Qed.

(* 須原さんの証明　※フルスクラッチ版(自分のスクリプトとは比較にならないほど素晴らしい！) *)
Variable M : bird.  (* ものまね鳥 *)
Variable P : bird.

(* ものまね鳥の定義 *)
Hypothesis mock : forall (x : bird), app M x = app x x.

(* 合成鳥の定義（作り方） *)  (* コメント：合成鳥Cが存在すると書かずに、直接作り方を書いているところが素晴らしい！ *)
Hypothesis comp : forall (A B x : bird), app A (app B x) = app (app A B) x.

Goal exists (x : bird), app P x = x.
Proof.
  move: (comp P M) => Hc.
  exists (app M (app P M)).
  by rewrite Hc mock.
Qed.
