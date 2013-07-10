(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred_laws.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Predicate Algebraic Laws *}

theory utp_pred_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  utp_subst_laws
begin

subsubsection {* Boolean Algebra laws *}

theorem AndP_comm :
"p1 \<and>\<^sub>p p2 = p2 \<and>\<^sub>p p1"
  by (utp_pred_auto_tac)

theorem AndP_idem [simp]:
"p \<and>\<^sub>p p = p"
  by (utp_pred_auto_tac)

theorem AndP_assoc :
"p1 \<and>\<^sub>p (p2 \<and>\<^sub>p p3) = (p1 \<and>\<^sub>p p2) \<and>\<^sub>p p3"
  by (utp_pred_auto_tac)

theorem AndP_OrP_distl :
"p1 \<and>\<^sub>p (p2 \<or>\<^sub>p p3) = (p1 \<and>\<^sub>p p2) \<or>\<^sub>p (p1 \<and>\<^sub>p p3)"
  by (utp_pred_auto_tac)

theorem AndP_OrP_distr:
"(p1 \<or>\<^sub>p p2) \<and>\<^sub>p p3 = (p1 \<and>\<^sub>p p3) \<or>\<^sub>p (p2 \<and>\<^sub>p p3)"
  by (utp_pred_auto_tac)

theorem OrP_comm :
"p1 \<or>\<^sub>p p2 = p2 \<or>\<^sub>p p1"
  by (utp_pred_auto_tac)

theorem OrP_idem [simp]:
"p \<or>\<^sub>p p = p"
  by (utp_pred_auto_tac)

theorem OrP_assoc :
"p1 \<or>\<^sub>p (p2 \<or>\<^sub>p p3) = (p1 \<or>\<^sub>p p2) \<or>\<^sub>p p3"
  by (utp_pred_auto_tac)

theorem OrP_AndP_distl :
"p1 \<or>\<^sub>p (p2 \<and>\<^sub>p p3) = (p1 \<or>\<^sub>p p2) \<and>\<^sub>p (p1 \<or>\<^sub>p p3)"
  by (utp_pred_auto_tac)

theorem OrP_AndP_distr :
"(p1 \<and>\<^sub>p p2) \<or>\<^sub>p p3 = (p1 \<or>\<^sub>p p3) \<and>\<^sub>p (p2 \<or>\<^sub>p p3)"
  by (utp_pred_auto_tac)

theorem AndP_contra :
"p \<and>\<^sub>p \<not>\<^sub>p p = false"
  by (utp_pred_auto_tac)

theorem OrP_excluded_middle :
"p \<or>\<^sub>p \<not>\<^sub>p p = true"
  by (utp_pred_auto_tac)

theorem OrP_ref :
"p1 \<or>\<^sub>p p2 \<sqsubseteq> p1"
  by (utp_pred_auto_tac)

lemma demorgan1: "\<not>\<^sub>p(x \<or>\<^sub>p y) = \<not>\<^sub>px \<and>\<^sub>p \<not>\<^sub>py"
  by (utp_pred_auto_tac)

lemma demorgan2: "\<not>\<^sub>p(x \<and>\<^sub>p y) = \<not>\<^sub>px \<or>\<^sub>p \<not>\<^sub>py"
  by (utp_pred_auto_tac)

lemma demorgan3: "x \<or>\<^sub>p y = \<not>\<^sub>p(\<not>\<^sub>px \<and>\<^sub>p \<not>\<^sub>py)"
  by (utp_pred_auto_tac)

lemma utp_pred_simps [simp]:
  "\<not>\<^sub>p false    = true"
  "\<not>\<^sub>p true     = false"
  "\<not>\<^sub>p \<not>\<^sub>p p = p"
  "false \<and>\<^sub>p x  = false" 
  "x \<and>\<^sub>p false  = false"
  "true \<and>\<^sub>p x   = x"
  "x \<and>\<^sub>p true   = x"
  "true \<or>\<^sub>p x   = true"
  "x \<or>\<^sub>p true   = true"
  "false \<or>\<^sub>p x  = x"
  "x \<or>\<^sub>p false  = x"
  "false \<Rightarrow>\<^sub>p x = true" 
  "true \<Rightarrow>\<^sub>p x  = x" 
  "p \<Rightarrow>\<^sub>p true = true" 
  "p \<Rightarrow>\<^sub>p false = \<not>\<^sub>p p"
  "P \<Leftrightarrow>\<^sub>p true = P" 
  "true \<Leftrightarrow>\<^sub>p P = P" 
  "P \<Leftrightarrow>\<^sub>p false = \<not>\<^sub>p P" 
  "false \<Leftrightarrow>\<^sub>p P = \<not>\<^sub>p P" 
  by (utp_pred_tac)+

subsection {* Introduction rules *}

lemma RefP_OrP: "p \<sqsubseteq> q \<longleftrightarrow> p = p \<or>\<^sub>p q"
  by (utp_pred_auto_tac)

lemma RefP_OrP_intro [intro]:
  "p \<or>\<^sub>p q = p \<Longrightarrow> p \<sqsubseteq> q"
  by (utp_pred_auto_tac)

lemma RefP_AndP: "p \<sqsubseteq> q \<longleftrightarrow> q = p \<and>\<^sub>p q"
  by (utp_pred_auto_tac)

lemma RefP_AndP_intro [intro]:
  "p \<and>\<^sub>p q = q \<Longrightarrow> p \<sqsubseteq> q"
  by (utp_pred_auto_tac)

lemma IffP_eq_intro [intro]:
  "p \<Leftrightarrow>\<^sub>p q \<Longrightarrow> p = q"
  by (utp_pred_auto_tac)

lemma ClosureP_intro: 
  "[p]\<^sub>p \<Longrightarrow> taut p"
  by (utp_pred_tac)

subsection {* Implication Laws *}

lemma ImpliesP_export:
  "p \<Rightarrow>\<^sub>p q = p \<Rightarrow>\<^sub>p (p \<and>\<^sub>p q)"
  by (utp_pred_tac)

lemma ImpliesP_eq_subst:
  "v \<rhd>\<^sub>e x \<Longrightarrow> ($\<^sub>ex ==\<^sub>p v \<Rightarrow>\<^sub>p p) = ($\<^sub>ex ==\<^sub>p v \<Rightarrow>\<^sub>p p[v/\<^sub>px])"
  apply (utp_pred_tac)
  apply (auto simp add:evale eval typing)
  apply (metis binding_upd_simps(2))+
done

subsection {* Quantifier Laws *}

theorem ExistsP_ident :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow> (\<exists>\<^sub>p vs . p) = p"
  by (utp_pred_tac)

theorem ForallP_ident :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow> (\<forall>\<^sub>p vs . p) = p"
  by (utp_pred_tac)

theorem ExistsP_union :
"(\<exists>\<^sub>p vs1 \<union> vs2 . p) = (\<exists>\<^sub>p vs1 . \<exists>\<^sub>p vs2 . p)"
apply (utp_pred_tac)
apply (auto)
apply (rule_tac x = "b'" in exI)
apply (rule_tac x = "b'" in exI)
apply (simp)+
apply (rule_tac x = "b' \<oplus>\<^sub>b b'a on vs2" in exI)
apply (simp add: binding_override_assoc)
done

theorem ForallP_union :
"(\<forall>\<^sub>p vs1 \<union> vs2 . p) = (\<forall>\<^sub>p vs1 . \<forall>\<^sub>p vs2 . p)"
  by (simp add: ForallP_def ExistsP_union UNREST_NotP NotP_NotP)

lemma ForallP_AndP_dist: 
  "(\<forall>\<^sub>p vs. p \<and>\<^sub>p q) = (\<forall>\<^sub>p vs. p) \<and>\<^sub>p (\<forall>\<^sub>p vs. q)"
  by (utp_pred_auto_tac)

lemma ClosureP_AndP_dist:
  "[p \<and>\<^sub>p q]\<^sub>p = [p]\<^sub>p \<and>\<^sub>p [q]\<^sub>p"
  by (utp_pred_auto_tac)

theorem ExistsP_OrP_dist:
"(\<exists>\<^sub>p vs. p1 \<or>\<^sub>p p2) = (\<exists>\<^sub>p vs. p1) \<or>\<^sub>p (\<exists>\<^sub>p vs. p2)"
  by (utp_pred_auto_tac)

theorem ExistsP_AndP_expand1:
"\<lbrakk>UNREST vs p2\<rbrakk> \<Longrightarrow>
 (\<exists>\<^sub>p vs. p1) \<and>\<^sub>p p2 = (\<exists>\<^sub>p vs. (p1 \<and>\<^sub>p p2))"
  by (utp_pred_tac)

theorem ExistsP_AndP_expand2:
"\<lbrakk>UNREST vs p1\<rbrakk> \<Longrightarrow>
 p1 \<and>\<^sub>p (\<exists>\<^sub>p vs. p2) = (\<exists>\<^sub>p vs. (p1 \<and>\<^sub>p p2))"
  by (utp_pred_tac)

text {* The one point rule *}
theorem ExistsP_one_point:
  "\<lbrakk> e \<rhd>\<^sub>e x; UNREST_EXPR {x} e \<rbrakk> \<Longrightarrow>
  (\<exists>\<^sub>p {x}. p \<and>\<^sub>p $\<^sub>ex ==\<^sub>p e) = p[e/\<^sub>px]"
  apply (auto simp add:eval evale typing defined)
  apply (rule_tac x="b(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>eb)" in exI)
  apply (simp)
done

lemma ExistsP_has_value:
  "\<lbrakk> UNREST_EXPR {x} v; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> (\<exists>\<^sub>p {x}. $\<^sub>ex ==\<^sub>p v) = true"
  apply (utp_pred_tac, utp_expr_tac)
  apply (auto)
  apply (rule_tac x="b(x :=\<^sub>b \<lbrakk>v\<rbrakk>\<^sub>eb)" in exI)
  apply (simp)
done

theorem ExistsP_SubstP_rename :
  "\<lbrakk> vtype x = vtype y; aux x = aux y; UNREST {x} p \<rbrakk> 
   \<Longrightarrow> (\<exists>\<^sub>p {y}. p) = (\<exists>\<^sub>p {x}. p[$\<^sub>ex/\<^sub>py])"
  apply (simp add:eval evale typing defined unrest binding_upd_twist)
  apply (clarify)
  apply (rule, erule exE)
  apply (rule_tac x="b(x :=\<^sub>b \<langle>b'\<rangle>\<^sub>b y)" in exI)
  apply (simp add:typing eval defined binding_upd_twist)
  apply (metis EvalP_UNREST_assign_1 binding_upd_twist binding_value_alt)
  apply (erule exE)
  apply (rule_tac x="b(y :=\<^sub>b \<langle>b'\<rangle>\<^sub>b x)" in exI)
  apply (simp add:typing eval defined binding_upd_twist)
  apply (metis EvalP_UNREST_assign_1 binding_upd_twist binding_value_alt)
done

subsection {* Expression theorems *}

lemma VarP_EqualP_aux:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
   ($\<^sub>px) = ($\<^sub>ex ==\<^sub>p TrueE)"
  apply (utp_pred_tac)
  apply (auto)
  apply (metis BOOL_SORT_class.Inverse FalseV_def MkBool_cases TrueV_def aux_defined binding_type)
done

lemma VarP_NotP_EqualP_aux:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
   (\<not>\<^sub>p $\<^sub>px) = $\<^sub>ex ==\<^sub>p FalseE"
  apply (utp_pred_tac)
  apply (auto)
  apply (metis BOOL_SORT_class.Inverse FalseV_def MkBool_cases TrueV_def aux_defined binding_type)
done

lemma expr_simps [simp]:
  "ExprP TrueE = TrueP"
  "ExprP FalseE = FalseP"
  by (utp_pred_tac)+

subsection {* Case splitting *}

ML {*
  structure ucases =
    Named_Thms (val name = @{binding ucases} val description = "case splitting theorems")
*}

setup ucases.setup

text {* A generic law for case splitting a variables *}

lemma utp_case_split_eq:
  "\<lbrakk> \<And> v. v \<rhd> x \<Longrightarrow> P[LitE v/\<^sub>px] = Q[LitE v/\<^sub>px] \<rbrakk> \<Longrightarrow> P = Q"
  apply (utp_pred_tac)
  apply (metis (full_types) binding_compat binding_upd_triv)
done

lemma BoolType_aux_cases:
  "(v :! BoolType) \<longleftrightarrow> v \<in> {TrueV, FalseV}"
  by (auto intro:typing)

lemma BoolType_aux_var_split_taut [ucases]:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
  [p]\<^sub>p = [p[FalseE/\<^sub>px] \<and>\<^sub>p p[TrueE/\<^sub>px]]\<^sub>p"
  apply (utp_pred_tac) 
  apply (metis FalseV_def MkBool_cases Rep_WF_BINDING_inverse TrueV_def aux_defined binding_type binding_upd_def fun_upd_idem_iff)
done

lemma BoolType_aux_var_split_exists [ucases]:
  "\<lbrakk> vtype x = BoolType; aux x \<rbrakk> \<Longrightarrow> 
   (\<exists>\<^sub>p {x}. P) = P[FalseE/\<^sub>px] \<or>\<^sub>p P[TrueE/\<^sub>px]"
  apply (utp_pred_tac)
  apply (auto)
  apply (metis FalseV_def MkBool_cases Rep_WF_BINDING TrueV_def WF_BINDING_app_type aux_defined)
  apply (metis BOOL_SORT_class.Defined MkBool_type binding_upd_apply var_compat_def)
  apply (metis BOOL_SORT_class.Defined MkBool_type binding_upd_apply var_compat_def)
done

lemma BoolType_aux_var_split_eq_intro [ucases]:
  assumes "vtype x = BoolType" "aux x" 
          "p[FalseE/\<^sub>px] = q[FalseE/\<^sub>px]"
          "p[TrueE/\<^sub>px] = q[TrueE/\<^sub>px]"
  shows "p = q"
  apply (rule IffP_eq_intro)
  apply (rule ClosureP_intro)
  apply (unfold BoolType_aux_var_split_taut[OF assms(1) assms(2), of "p \<Leftrightarrow>\<^sub>p q"])
  apply (simp add:usubst assms)
  apply (utp_pred_tac)
done

subsection {* Typing theorems *}

lemma MkBool_True_compat [typing]: 
  "vtype x = BoolType \<Longrightarrow> MkBool True \<rhd> x"
  by (metis BOOL_SORT_class.Defined MkBool_type var_compat_intros(1))

lemma MkBool_False_compat [typing]: 
  "vtype x = BoolType \<Longrightarrow> MkBool False \<rhd> x"
 by (metis BOOL_SORT_class.Defined MkBool_type var_compat_intros(1))

subsection {* Uniqueness Theorems *}

lemma VarP_not_false [simp]:
  "vtype x = BoolType \<Longrightarrow> $\<^sub>px \<noteq> false"
  "vtype x = BoolType \<Longrightarrow>  false \<noteq> $\<^sub>px"
  by (utp_pred_tac, rule_tac x="\<B>(x :=\<^sub>b MkBool True)" in exI, simp add:typing)+

lemma VarP_not_true [simp]:
  "vtype x = BoolType \<Longrightarrow> $\<^sub>px \<noteq> true"
  "vtype x = BoolType \<Longrightarrow>  true \<noteq> $\<^sub>px"
  by (utp_pred_tac, rule_tac x="\<B>(x :=\<^sub>b MkBool False)" in exI, simp add:typing)+

lemma NotP_not_false [simp]:
  "x \<noteq> true \<Longrightarrow> \<not>\<^sub>p x \<noteq> false"
  "x \<noteq> false \<Longrightarrow> \<not>\<^sub>p x \<noteq> true"
  by (utp_pred_tac)+

end