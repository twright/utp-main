section \<open> Calculations \<close>

theory tcircus_calc
  imports tcircus_idle tcircus_timed_conj
begin

abbreviation tsyme :: "('e reftrace, 's) uexpr \<Rightarrow> ('s, 'e) taction" where
"tsyme t \<equiv> U(\<exists> t\<^sub>0. $tr\<acute> = $tr @ \<guillemotleft>t\<^sub>0\<guillemotright> \<and> t\<^sub>0 \<subseteq>\<^sub>t \<lceil>t\<rceil>\<^sub>S\<^sub><)"

utp_const tsyme

lemma foldr_concat_eval [uexpr_transfer_extra]: "\<lbrakk>foldr (bop (@)) xs t\<rbrakk>\<^sub>e s = concat (map (\<lambda> e. \<lbrakk>e\<rbrakk>\<^sub>e s) xs) @ \<lbrakk>t\<rbrakk>\<^sub>e s"
  by (induct xs, rel_auto+)

definition [upred_defs]: "tc_time' X t = U(replicate t (Tock (-X)))"

utp_const tc_time'

text \<open> We introduce a small algebra for peri- and postconditions to capture timed behaviours. The
  first operator captures stable intermediate (i.e. quiescent) behaviours. Here, @{term s} is a 
  predicate on the state (a condition), @{term t} is a trace over non-tock events, and @{term E} 
  is the set of events being accepted at this point. FIXME: Should stable observations
  also update the state? \<close>

definition tc_stable :: "'s upred \<Rightarrow> ('e reftrace, 's) uexpr \<Rightarrow> ('e set, 's) uexpr \<Rightarrow> 's upred \<Rightarrow> ('s, 'e) taction" ("\<E>'(_, _, _, _')") where
[upred_defs]: "\<E>(s,t,E,p) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin>\<^sub>\<R> $ref\<acute>) \<and> ((\<lceil>p\<rceil>\<^sub>S\<^sub>< \<Rightarrow> ($pat\<acute>))))"

text \<open> We also need unstable intermediate observations, which the following relation provides. It
  has no set associated, since no refusal set is observed. \<close>

definition tc_unstable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<U>'(_, _')") where
[upred_defs]: "\<U>(s,t) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute>)"

text \<open> A final observation is similar to a stable observation, except it can update the state 
  variables and does not characterise a refusal set. \<close>

definition tc_final :: "'s upred \<Rightarrow>('e tev list, 's) uexpr \<Rightarrow> 's usubst \<Rightarrow> ('s, 'e) taction" ("\<F>'(_, _, _')") where
[upred_defs]: "\<F>(s,t,\<sigma>) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)" 
  
text \<open> A timed observation represents a period of delay. The set @{term X} characterises the set of
  events that are accepted during this period. The set @{term A} characterises the possible delay
  periods, for example @{term "{0..n}"} means a delay of between $0$ and $n$ units. \<close>

definition tc_time :: "('e set, 's) uexpr \<Rightarrow> (nat set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<T>'(_, _')") where 
[upred_defs]: "\<T>(X, A) = U(\<exists> t \<in> tocks \<lceil>-X\<rceil>\<^sub>S\<^sub><. ($tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright>) \<and> (length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub><) \<and> ($st\<acute> = $st))"

utp_lift_notation tc_stable
utp_lift_notation tc_unstable
utp_lift_notation tc_final (2)
utp_lift_notation tc_time

lemma [closure]: "\<E>(s, t, E, p) is TRR"
  by (rel_auto)

lemma [closure]: "\<E>(s, t, E, p) is TDC"
  by (rel_auto, (meson refusal_mp)+)

lemma [closure]: "\<U>(s, t) is TRR"
  by (rel_auto)

lemma [closure]: "\<F>(s, t, \<sigma>) is TRR"
  by (rel_auto)

lemma [closure]: "\<T>(X, A) is TRR"
  by (rel_auto)

lemma [closure]: "\<T>(X, A) is TIP"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<E>(s, t, E, p)"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<U>(s, t)"
  by (rel_auto)

text \<open> Unstable observations are subsumed by stable ones \<close>

(* TODO: Should this be true? *)
lemma patient_instability_subsumed: "\<E>(s, t, E, true) \<sqsubseteq> \<U>(s, t)"
  apply (rel_auto)
  done

lemma insistant_instability_subsumed: "\<E>(s, t, E, false) \<sqsubseteq> \<U>(s, t)"
  by (rel_auto)

lemma instability_subsumed: "\<E>(s, t, E, p) \<sqsubseteq> \<U>(s, t)"
  by (rel_auto)

(* Original version was p1 \<and> p2 *)
lemma "(\<E>(s\<^sub>1, t, E\<^sub>1, p\<^sub>1) \<and> \<E>(s\<^sub>2, t, E\<^sub>2, p\<^sub>2)) = \<E>(s\<^sub>1 \<and> s\<^sub>2, t, E\<^sub>1 \<union> E\<^sub>2, p\<^sub>1 \<or> p\<^sub>2)"
  by (rel_auto)

lemma tconj_rfset:
  "(\<E>(s\<^sub>1,t,E\<^sub>1,p\<^sub>1) \<squnion>\<^sub>t \<E>(s\<^sub>2, t, E\<^sub>2, p\<^sub>2)) = \<E>(s\<^sub>1 \<and> s\<^sub>2, t, E\<^sub>1 \<union> E\<^sub>2, p\<^sub>1 \<and> p\<^sub>2)"
  apply (trr_auto)
  apply (smt (z3) Un_iff)
  apply (metis Un_iff)
  done

lemma stability_modulo_ref: "(\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<E>(s, t, E, p)) = (\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<U>(s, t))"
  by (rel_auto)

lemma tc_final_compose [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>\<^sub>1) ;; \<F>(s\<^sub>2, t\<^sub>2, \<sigma>\<^sub>2) = \<F>(s\<^sub>1 \<and> \<sigma>\<^sub>1 \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma>\<^sub>1 \<dagger> t\<^sub>2, \<sigma>\<^sub>2 \<circ>\<^sub>s \<sigma>\<^sub>1)"
  apply (trr_auto)
  using tock_ord_append apply blast
  apply (metis append_take_drop_id tock_ord_decompose)
  done

utp_const UINFIMUM (1) USUPREMUM (1)

lemma time_stable_compose:
  "\<T>(X, A) ;; \<E>(s, t, E, p) = (\<Sqinter> n \<bullet> \<E>(n \<in> A \<and> s, bop (^) [Tock (-X)] n @ t, E, p))"
  apply (trr_auto)
  apply (metis lit.rep_eq tock_ord_append tocks_order_power)
  apply (metis lit.rep_eq tock_ord_append tocks_order_power)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  done

lemma time_unstable_compose:
  "\<T>(X, A) ;; \<U>(s, t) = (\<Sqinter> n \<bullet> \<U>(\<guillemotleft>n\<guillemotright> \<in> A \<and> s, bop (^) [Tock (-X)] \<guillemotleft>n\<guillemotright> @ t))"
  apply (trr_auto)
  apply (metis tock_ord_append tocks_order_power)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  done

lemma time_final_compose:
  "\<T>(X, A) ;; \<F>(s, t, \<sigma>) = (\<Sqinter> n \<bullet> \<F>(\<guillemotleft>n\<guillemotright> \<in> A \<and> s, bop (^) [Tock (-X)] \<guillemotleft>n\<guillemotright> @ t, \<sigma>))"
  apply (trr_auto)
  apply (metis tock_ord_append tocks_order_power)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  done

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<E>(s\<^sub>2, t\<^sub>2, E, p) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> E, \<sigma> \<dagger> p)"
  apply (trr_auto)
  apply (metis tock_ord_append)
  using tock_ord_append apply blast
  apply (metis append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
   apply (metis append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  done

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<U>(s\<^sub>2, t\<^sub>2) = \<U>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  apply (trr_auto)
  apply (metis tock_ord_append)
  apply (metis append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  done

lemma [rpred]: "\<T>(X, {}) = false"
  by (rel_auto)

lemma [rpred]: "\<T>(X, {0}) = (II\<^sub>t)"
  by (rel_auto)

lemma [rpred]: "\<F>(true, [], id\<^sub>s) = II\<^sub>t"
  by (rel_simp)

lemma time_single_single [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n}) = \<T>(X, {m+n})"
  by (trr_auto)
     (metis (mono_tags, hide_lams) add_right_cancel append_take_drop_id length_append length_drop plus_list_def tocks_append trace_class.add_diff_cancel_left)

lemma time_single_lessthan [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..<n}) = \<T>(X, {m..<m+n})"
  by trr_auto
     (metis (no_types, lifting) add_left_strict_mono add_right_cancel append_take_drop_id diff_add_cancel_left' length_append length_drop tocks_append)

lemma time_single_atMost [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..n}) = \<T>(X, {m..m+n})"
  by trr_auto
     (metis (no_types, hide_lams) add_le_cancel_left add_right_cancel append_take_drop_id diff_add_cancel_left' length_append length_drop tocks_append)

lemma time_single_atLeast [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n..}) = \<T>(X, {m+n..})"
  apply trr_auto
  apply (rename_tac t s)
  apply (rule_tac x="take (\<lbrakk>m\<rbrakk>\<^sub>e s) t" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e s) t" in bexI)
  apply (auto)
  done

lemma split_time_dom:
  fixes l :: nat
  assumes "m\<^sub>1 + m\<^sub>2 \<le> l" "l \<le> m\<^sub>1 + m\<^sub>2 + (n\<^sub>1 + n\<^sub>2)"
  shows "(\<exists> n. n \<le> l \<and> m\<^sub>1 \<le> n \<and> m\<^sub>2 + n \<le> l \<and> n \<le> m\<^sub>1+n\<^sub>1 \<and> l \<le> m\<^sub>2+n\<^sub>2+n)"
  using assms
  by presburger

lemma [rpred]: "\<T>(X, {m\<^sub>1..m\<^sub>1+n\<^sub>1}) ;; \<T>(X, {m\<^sub>2..m\<^sub>2+n\<^sub>2}) = \<T>(X, {m\<^sub>1 + m\<^sub>2..m\<^sub>1 + m\<^sub>2+(n\<^sub>1 + n\<^sub>2)})"
proof (trr_auto)
  fix t s

  assume a: "t \<in> tocks (- \<lbrakk>X\<rbrakk>\<^sub>e s)" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s \<le> length t" "length t \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s + (\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e s)"
  then obtain n where n: "n \<le> length t" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s \<le> n" "\<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s + n \<le> length t" "n \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s+\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e s" "length t \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s+\<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e s+n"
    using split_time_dom by blast

  with a show "\<exists>tr. tr \<in> tocks (- \<lbrakk>X\<rbrakk>\<^sub>e s) \<and>
                \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s \<le> length tr \<and>
                length tr \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e s \<and> (\<exists>x\<in>tocks (- \<lbrakk>X\<rbrakk>\<^sub>e s). t = tr @ x \<and> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s \<le> length x \<and> length x \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e s)"
    apply (rule_tac x="take n t" in exI)
    apply (auto)
    apply (rule_tac x="drop n t" in bexI)
     apply (auto)
    done
qed

(* Changes from true to false *)
(*
lemma idle_true [rpred]: "idle(true) = \<T>({}, {0..}) ;; \<E>(true, [], {}, true)"
  by rel_auto
*)

lemma [rpred]: "idle\<^sub>I(\<T>(X, A)) = \<T>(X, A)" 
  by (rel_auto, simp add: tocks_subset) 

(*
lemma [rpred]: "idle(\<T>(X, A)) = \<T>(X, A) \<and> U($pat\<acute> = [True]\<^sub>\<P>)" 
  by (rel_auto, simp add: tocks_subset)
*)

lemma time_tocks_stable_insistant [rpred]: "idle\<^sub>I(\<T>(X, A) ;; \<E>(s, [], E, p)) = \<T>(X, A) ;; \<E>(s, [], E, p)"
  by (rel_auto; simp add: tocks_subset)

(*
lemma time_tocks_stable [rpred]: "idle(\<T>(X, A) ;; \<E>(s, [], E, p)) = (\<T>(X, A) ;; \<E>(s, [], E, True))"
  by (rel_auto; simp add: tocks_subset)
*)

lemma [rpred]: "idle\<^sub>I(\<T>(X, A) ;; \<U>(s, [])) = \<T>(X, A) ;; \<U>(s, [])"
  by (rel_auto, simp add: tocks_subset)

(*
lemma [rpred]: "idle(\<T>(X, A) ;; \<U>(s, [])) = \<T>(X, A) ;; \<U>(s, [])"
  by (rel_auto, simp add: tocks_subset)
*)

lemma [rpred]: "idle\<^sub>I(\<E>(s, [], E, p)) = \<E>(s, [], E, p)"
  by (rel_auto)

(*
lemma [rpred]: "idle(\<E>(s, [], E, p)) = \<E>(s, [], E, True)"
  by (rel_auto)
*)

lemma [rpred]: "idle\<^sub>I(\<E>(s, Evt t # ts, E, p)) = false"
  by (rel_simp)

lemma [rpred]: "idle(\<E>(s, Evt t # ts, E, p)) = false"
  by (rel_simp)

lemma [rpred]: "idle\<^sub>I(\<U>(s, Evt t # ts)) = false"
  by (rel_simp)

lemma [rpred]: "idle(\<U>(s, Evt t # ts)) = false"
  by (rel_simp)

lemma [rpred]: "(\<T>(X\<^sub>1, A\<^sub>1) \<and> \<T>(X\<^sub>2, A\<^sub>2)) = \<T>(X\<^sub>1 \<union> X\<^sub>2, A\<^sub>1 \<inter> A\<^sub>2)"
  by (rel_auto)

lemma [rpred]: "((\<T>(X\<^sub>1, A\<^sub>1)) \<squnion>\<^sub>t (\<T>(X\<^sub>2, A\<^sub>2))) = \<T>(X\<^sub>1 \<union> X\<^sub>2, A\<^sub>1 \<inter> A\<^sub>2)"
  by (rel_auto)

lemma [rpred]: "((\<T>(A, T\<^sub>1) ;; \<E>(s\<^sub>1, [], {}, true)) \<squnion>\<^sub>t (\<T>(B, T\<^sub>2) ;; \<E>(s\<^sub>2, [], {}, true))) 
       = \<T>(A \<union> B, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, [], {}, true)"
  apply(trr_auto)
  done

lemma [rpred]: "(\<T>(A, T\<^sub>1) ;; \<E>(s\<^sub>1, [], {}, true) \<and> \<T>(B, T\<^sub>2) ;; \<E>(s\<^sub>2, [], {}, true)) 
       = \<T>(A \<union> B, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, [], {}, true)"
  by (rel_auto)

lemma [rpred]: "((\<T>(A, T\<^sub>1) ;; \<E>(s\<^sub>1, [], {}, true)) \<squnion>\<^sub>t (\<T>(B, T\<^sub>2) ;; \<E>(s\<^sub>2, [], {}, true))) 
       = \<T>(A \<union> B, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, [], {}, true)"
  by (rel_auto; blast)
lemma [rpred]: "(\<T>(X, A) ;; \<E>(true, [], E\<^sub>1, p\<^sub>1) \<and> \<T>(Y, B) ;; \<E>(true, [], E\<^sub>2, p\<^sub>2)) = \<T>(X \<union> Y, A \<inter> B) ;; \<E>(true, [], E\<^sub>1 \<union> E\<^sub>2, p\<^sub>1 \<or> p\<^sub>2)"
  by (rel_auto)

lemma [rpred]: "((\<T>(X, A) ;; \<E>(true, [], E\<^sub>1, p\<^sub>1)) \<squnion>\<^sub>t (\<T>(Y, B) ;; \<E>(true, [], E\<^sub>2, p\<^sub>2)))
              = \<T>(X \<union> Y, A \<inter> B) ;; \<E>(true, [], E\<^sub>1 \<union> E\<^sub>2, p\<^sub>1 \<and> p\<^sub>2)"
  apply (trr_simp)
  apply(safe)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply (smt (z3) Un_iff tocks_inter1 tocks_inter2)+
  done

lemma nat_set_simps [simp]:
  fixes m::"(nat, _) uexpr"
  shows "U({0..<m} \<inter> {m}) = U({})" "U(A \<inter> A) = U(A)"
  by (rel_simp+)

lemma [rpred]: "active\<^sub>I(\<U>(s, [])) = false"
  by (rel_auto)

lemma [rpred]: "idle\<^sub>I(\<U>(s, [])) = \<U>(s, [])"
  by (rel_auto)

lemma [rpred]: "active(\<U>(s, [])) = false"
  by (rel_auto)

(*
lemma [rpred]: "idle(\<U>(s, [])) = \<U>(s, [])"
  by (rel_auto)
*)

(*
lemma [rpred]: "(true \<squnion>\<^sub>t \<U>(true, [])) = true"
  apply (rel_auto)
*)

lemma [rpred]: "(P \<squnion>\<^sub>t false) = false" "(false \<squnion>\<^sub>t P) = false"
  by (rel_auto+)

lemma [rpred]:
  assumes "P is TRR" "P is TRR6"
  shows "time\<^sub>I(P ;; \<U>(true, [])) = time\<^sub>I(P)"
proof -
  have "time\<^sub>I(TRR(P) ;; \<U>(true, [])) = time\<^sub>I(TRR P)"
    apply (trr_auto cls: assms)
    oops
(*
  thus "time(P ;; \<U>(true, [])) = time(P)" "time\<^sub>I(P ;; \<U>(true, [])) = time\<^sub>I(P)"
    by (simp_all add: Healthy_if assms)
qed
*)

lemma [rpred]: "idle\<^sub>I(\<T>(X, T) ;; \<U>(true, [Evt a])) = false"
  by (rel_simp)

lemma [rpred]: "idle(\<T>(X, T) ;; \<U>(true, [Evt a])) = false"
  by (rel_simp)

lemma [simp]: "U(insert x (insert x A)) = U(insert x A)"
  by (rel_auto)

lemma [rpred]: "active\<^sub>I(\<T>(X, {0..})) = false"
  by (rel_auto)

lemma [rpred]: "active(\<T>(X, {0..})) = false"
  by (rel_auto)

lemma [rpred]: "active\<^sub>I(\<T>(X, T) ;; \<U>(s, [])) = false"
  by (trr_auto)

lemma active_uns [rpred]:
  assumes "P is TRR"
  shows "active\<^sub>I(P ;; \<U>(true, [])) = active\<^sub>I(P) ;; \<U>(true, [])"
proof -
  have "active\<^sub>I(TRR(P) ;; \<U>(true, [])) = active\<^sub>I(TRR P) ;; \<U>(true, [])"
    by (rel_blast+)
  thus "active\<^sub>I(P ;; \<U>(true, [])) = active\<^sub>I(P) ;; \<U>(true, [])"
    by (simp_all add: Healthy_if assms)
qed

(*
lemma [rpred]: "active(\<T>(X, T) ;; \<U>(s, [])) = false"
  by (trr_auto)
*)

lemma [rpred]: "(\<T>({}, {0..}) ;; \<E>(true, [], {}, false) \<and> idle\<^sub>I(P)) = idle\<^sub>I(P)"
  by (rel_auto)

lemma [rpred]: "(\<T>({}, {0..}) ;; \<E>(true, [], {}, false) \<and> idle(P)) = idle(P)"
  by (rel_auto)

lemma [rpred]:
  assumes "P is TRR"
  shows "((\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t idle\<^sub>I(P)) = idle\<^sub>I(P)"
proof -
  have 1: "P = TRR6(P)"
    by (metis Healthy_if TRR_TRRw TRR_def assms)
  have 2: "TRR6(P) is TRR"
    using "1" assms by force
  show ?thesis
    apply(subst (2 1) 1)
    apply(trr_auto cls: 2)
    apply metis
    done
qed


lemma [rpred]:
  assumes "P is TRF"
  shows "time\<^sub>I(P ;; \<U>(true, [])) = time\<^sub>I(P)"
proof -
  have "time\<^sub>I(TRF(P) ;; \<U>(true, [])) = time\<^sub>I(TRF(P))"
    apply(trr_auto cls: assms)
    apply blast+
    done
  thus "time\<^sub>I(P ;; \<U>(true, [])) = time\<^sub>I(P)"
    by (simp_all add: Healthy_if assms)
qed

(*
lemma [rpred]:
  assumes "P is TRR" "P is TRR7"
  shows "((\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t idle\<^sub>I(P)) = idle\<^sub>I(P)"
proof -
  have 1: "P = TRR7(P)"
    by (simp add: Healthy_if assms(2))
  have 2: "TRR7 P is TRR"
    sorry
  show ?thesis
    apply(subst (2 1) 1)
    apply(trr_auto cls: assms)
    sledgehammer
    done
qed
*)
(*
  sledgehammer
  by fastforce
*)

lemma [rpred]: "((\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t idle(P)) = idle(P)"
  apply (rel_auto)
  oops
(*
  by (metis Prefix_Order.prefixE append_minus patience.distinct(1))
*)

(*  by fastforce *)

lemma unstable_TRF:
  assumes "P is TRF"
  shows "P ;; \<U>(true, []) = U((\<exists> $st\<acute> \<bullet> P) \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute>)"
proof -
  have "TRF P ;; \<U>(true, []) = U((\<exists> $st\<acute> \<bullet> TRF P) \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute>)"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

text \<open> If a pericondition @{term P} contains an unstable version of each postcondition observation
  in @{term Q}, then every time trace of the @{term P} has an extension in @{term Q}. \<close>

lemma time_peri_in_post_insistant:
  assumes "P is TRR" "P is TIP" "Q is TRF" "P \<sqsubseteq> Q ;; \<U>(true, [])"
  shows "time\<^sub>I(P) \<sqsubseteq> Q"
proof -
  have "Q ;; \<U>(true, []) ;; II\<^sub>t \<sqsubseteq> Q"
    apply (trr_simp cls: assms)
    by blast
  also have "P ;; II\<^sub>t \<sqsubseteq> ..."
    by (simp add: RA1 assms(4) urel_dioid.mult_isor)
  also have "time\<^sub>I(P) ;; II\<^sub>t \<sqsubseteq> ..."
    by (simp add: TIP_has_time assms(1) assms(2) urel_dioid.mult_isor utp_pred_laws.inf.orderI)
  also have "... = time\<^sub>I(P)"
    apply(rule TRF_right_unit)
    apply (simp add: TRF_right_unit TRF_time_insistant assms)
    done
  finally show ?thesis .
qed

(*
lemma time_peri_in_post:
  assumes "P is TRR" "P is TIP" "Q is TRF" "P \<sqsubseteq> Q ;; \<U>(true, [])"
  shows "time(P) \<sqsubseteq> Q"
proof -
  have "Q ;; \<U>(true, []) ;; II\<^sub>t \<sqsubseteq> Q"
    by (trr_auto cls: assms, blast)
  also have "P ;; II\<^sub>t \<sqsubseteq> ..."
    by (simp add: RA1 assms(4) urel_dioid.mult_isor)
  also have "time(P) ;; II\<^sub>t \<sqsubseteq> ..."
    by (simp add: TIP_has_time assms(1) assms(2) urel_dioid.mult_isor utp_pred_laws.inf.orderI)
  also have "... = time(P)"
    by (simp add: TRF_right_unit TRF_time assms(1))
  finally show ?thesis .
qed
*)

(*
lemma TRR_conj_time [rpred]:
  assumes "P is TRR" "P is TRR6"
  shows "(time\<^sub>I(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<and> P) = P"
proof -
  have "(time\<^sub>I(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<and> TRR(P)) = TRR(P)"
    apply(trr_auto cls: assms)
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
*)

lemma TRR_tconj_time [rpred]:
  assumes "P is TRR"
  shows "((time\<^sub>I(\<T>({}, {0..}) ;; \<E>(true, [], {}, true))) \<squnion>\<^sub>t P) = P"
  apply(trr_auto cls: assms)
  oops

(*
proof -
  have 1: "((time\<^sub>I(\<T>({}, {0..}))) ;; \<E>(true, [], {}, true)) = (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))"
    by (rel_auto)
  have 2: "(time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)) = ((\<exists> $pat\<acute> \<bullet> (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))) \<and> $pat\<acute>)"
    by rel_auto
  have "(time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P)) = (((time\<^sub>I(\<T>({}, {0..})) \<and> $pat\<acute>) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P))"
    apply(rel_blast)
    done
  also have "\<dots> = ((time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P))"
    apply(simp add: 1)
    done
  also have "\<dots> = (((\<exists> $pat\<acute> \<bullet> (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))) \<and> $pat\<acute>) \<squnion>\<^sub>t TRR(P))"
    by (metis "2")
  also have "\<dots> = (TRR(P) \<squnion>\<^sub>t ((\<exists> $pat\<acute> \<bullet> (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))) \<and> $pat\<acute>))"
    by (simp add: tconj_comm)
  also have "\<dots> = (TRR(P) \<and> (\<exists> $pat\<acute> \<bullet> time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)))"
    apply(auto simp add: conj_tconj unrest)
    done
  also have "\<dots> = ((\<exists> $pat\<acute> \<bullet> time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)) \<and> TRR(P))"
    apply(rel_blast)
    done
  also have "\<dots> = ((time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, false)) \<and> TRR(P))"
    apply(rel_blast)
    done
  also have "\<dots> = TRR P"
    apply(rel_blast)
    done
  finally have "(time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P)) = TRR(P)" .
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
*)

(*
lemma TRR_tconj_time [rpred]:
  assumes "P is TRR"
  shows "((time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true))) \<squnion>\<^sub>t P) = P"
proof -
  have 1: "((time\<^sub>I(\<T>({}, {0..})) \<and> $pat\<acute>) ;; \<E>(true, [], {}, true)) = (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))"
    by (rel_auto)
  have 2: "(time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)) = ((\<exists> $pat\<acute> \<bullet> (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))) \<and> $pat\<acute>)"
    by rel_auto
  have "(time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P)) = (((time\<^sub>I(\<T>({}, {0..})) \<and> $pat\<acute>) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P))"
    apply(rel_blast)
    done
  also have "\<dots> = ((time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P))"
    apply(simp add: 1)
    done
  also have "\<dots> = (((\<exists> $pat\<acute> \<bullet> (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))) \<and> $pat\<acute>) \<squnion>\<^sub>t TRR(P))"
    by (metis "2")
  also have "\<dots> = (TRR(P) \<squnion>\<^sub>t ((\<exists> $pat\<acute> \<bullet> (time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true))) \<and> $pat\<acute>))"
    by (simp add: tconj_comm)
  also have "\<dots> = (TRR(P) \<and> (\<exists> $pat\<acute> \<bullet> time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)))"
    apply(auto simp add: conj_tconj unrest)
    done
  also have "\<dots> = ((\<exists> $pat\<acute> \<bullet> time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, true)) \<and> TRR(P))"
    apply(rel_blast)
    done
  also have "\<dots> = ((time\<^sub>I(\<T>({}, {0..})) ;; \<E>(true, [], {}, false)) \<and> TRR(P))"
    apply(rel_blast)
    done
  also have "\<dots> = TRR P"
    apply(rel_blast)
    done
  finally have "(time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<squnion>\<^sub>t TRR(P)) = TRR(P)" .
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
*)

end