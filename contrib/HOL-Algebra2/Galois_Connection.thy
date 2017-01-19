theory Galois_Connection
  imports Complete_Lattice
begin

section {* Galois connections *}

subsection {* Definition and basic properties *}

record ('a, 'b, 'c, 'd) galcon =
  orderA :: "('a, 'c) gorder_scheme" ("\<X>\<index>")
  orderB :: "('b, 'd) gorder_scheme" ("\<Y>\<index>")
  lower  :: "'a \<Rightarrow> 'b" ("\<pi>\<^sup>*\<index>")
  upper  :: "'b \<Rightarrow> 'a" ("\<pi>\<^sub>*\<index>")

type_synonym ('a, 'b) galois = "('a, 'b, unit, unit) galcon"

abbreviation "inv_galcon G \<equiv> \<lparr> orderA = inv_gorder \<Y>\<^bsub>G\<^esub>, orderB = inv_gorder \<X>\<^bsub>G\<^esub>, lower = upper G, upper = lower G \<rparr>"

definition comp_galcon :: "('b, 'c) galois \<Rightarrow> ('a, 'b) galois \<Rightarrow> ('a, 'c) galois" (infixr "\<circ>\<^sub>g" 85)
where "G \<circ>\<^sub>g F = \<lparr> orderA = orderA F, orderB = orderB G, lower = lower G \<circ> lower F, upper = upper F \<circ> upper G \<rparr>"

definition id_galcon :: "'a gorder \<Rightarrow> ('a, 'a) galois" ("I\<^sub>g") where
"I\<^sub>g(A) = \<lparr> orderA = A, orderB = A, lower = id, upper = id \<rparr>"

locale connection =
  fixes G (structure)
  assumes is_order_A: "partial_order \<X>"
  and is_order_B: "partial_order \<Y>"
  and lower_closure: "\<pi>\<^sup>* \<in> carrier \<X> \<rightarrow> carrier \<Y>"
  and upper_closure: "\<pi>\<^sub>* \<in> carrier \<Y> \<rightarrow> carrier \<X>"

locale galois_connection = connection +
  assumes galois_property: "\<lbrakk>x \<in> carrier \<X>; y \<in> carrier \<Y>\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
begin

  lemma is_weak_order_A: "weak_partial_order \<X>"
  proof -
    interpret po: partial_order \<X>
      by (metis is_order_A)
    show ?thesis ..
  qed

  lemma is_weak_order_B: "weak_partial_order \<Y>"
  proof -
    interpret po: partial_order \<Y>
      by (metis is_order_B)
    show ?thesis ..
  qed

  lemma right: "\<lbrakk>x \<in> carrier \<X>; y \<in> carrier \<Y>; \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
    by (metis galois_property)

  lemma left: "\<lbrakk>x \<in> carrier \<X>; y \<in> carrier \<Y>; x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y"
    by (metis galois_property)

  lemma deflation: "y \<in> carrier \<Y> \<Longrightarrow> \<pi>\<^sup>* (\<pi>\<^sub>* y) \<sqsubseteq>\<^bsub>\<Y>\<^esub> y"
    by (metis Pi_iff is_weak_order_A left lower_closure upper_closure weak_partial_order.le_refl)

  lemma inflation: "x \<in> carrier \<X> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* (\<pi>\<^sup>* x)"
    by (metis (no_types, lifting) PiE galois_connection.right galois_connection_axioms is_weak_order_B lower_closure upper_closure weak_partial_order.le_refl)

  lemma lower_iso: "isotone \<X> \<Y> \<pi>\<^sup>*"
  proof (auto simp add:isotone_def)
    show "weak_partial_order \<X>"
      by (metis is_weak_order_A)
    show "weak_partial_order \<Y>"
      by (metis is_weak_order_B)
    fix x y
    assume a: "x \<in> carrier \<X>" "y \<in> carrier \<X>" "x \<sqsubseteq>\<^bsub>\<X>\<^esub> y"
    have b: "\<pi>\<^sup>* y \<in> carrier \<Y>"
      using a(2) lower_closure by blast
    then have "\<pi>\<^sub>* (\<pi>\<^sup>* y) \<in> carrier \<X>"
      using upper_closure by blast
    then have "x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* (\<pi>\<^sup>* y)"
      by (meson a inflation is_weak_order_A weak_partial_order.le_trans)
    thus "\<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> \<pi>\<^sup>* y"
      by (meson b a(1) Pi_iff galois_property lower_closure upper_closure)
  qed

  lemma upper_iso: "isotone \<Y> \<X> \<pi>\<^sub>*"
    apply (auto simp add:isotone_def)
    apply (metis is_weak_order_B)
    apply (metis is_weak_order_A)
    apply (metis (no_types, lifting) Pi_mem deflation is_weak_order_B lower_closure right upper_closure weak_partial_order.le_trans)
  done

  lemma lower_comp: "x \<in> carrier \<X> \<Longrightarrow> \<pi>\<^sup>* (\<pi>\<^sub>* (\<pi>\<^sup>* x)) = \<pi>\<^sup>* x"
    by (meson deflation funcset_mem inflation is_order_B lower_closure lower_iso partial_order.le_antisym upper_closure use_iso2)

  lemma lower_comp': "x \<in> carrier \<X> \<Longrightarrow> (\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>*) x = \<pi>\<^sup>* x"
    by (simp add: lower_comp)

  lemma upper_comp: "y \<in> carrier \<Y> \<Longrightarrow> \<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* y)) = \<pi>\<^sub>* y"
  proof -
    assume a1: "y \<in> carrier \<Y>"
    hence f1: "\<pi>\<^sub>* y \<in> carrier \<X>" using upper_closure by blast 
    have f2: "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<sqsubseteq>\<^bsub>\<Y>\<^esub> y" using a1 deflation by blast
    have f3: "\<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* y)) \<in> carrier \<X>"
      using f1 lower_closure upper_closure by auto 
    have "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<in> carrier \<Y>" using f1 lower_closure by blast   
    thus "\<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* y)) = \<pi>\<^sub>* y"
      by (meson a1 f1 f2 f3 inflation is_order_A partial_order.le_antisym upper_iso use_iso2) 
  qed

  lemma upper_comp': "y \<in> carrier \<Y> \<Longrightarrow> (\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>*) y = \<pi>\<^sub>* y"
    by (simp add: upper_comp)

  lemma adjoint_idem1: "idempotent \<Y> (\<pi>\<^sup>* \<circ> \<pi>\<^sub>*)"
    by (simp add: idempotent_def is_order_B partial_order.eq_is_equal upper_comp)

  lemma adjoint_idem2: "idempotent \<X> (\<pi>\<^sub>* \<circ> \<pi>\<^sup>*)"
    by (simp add: idempotent_def is_order_A partial_order.eq_is_equal lower_comp)

  lemma fg_iso: "isotone \<Y> \<Y> (\<pi>\<^sup>* \<circ> \<pi>\<^sub>*)"
    by (metis iso_compose lower_closure lower_iso upper_closure upper_iso)

  lemma gf_iso: "isotone \<X> \<X> (\<pi>\<^sub>* \<circ> \<pi>\<^sup>*)"
    by (metis iso_compose lower_closure lower_iso upper_closure upper_iso)

  lemma semi_inverse1: "x \<in> carrier \<X> \<Longrightarrow> \<pi>\<^sup>* x = \<pi>\<^sup>* (\<pi>\<^sub>* (\<pi>\<^sup>* x))"
    by (metis lower_comp)

  lemma semi_inverse2: "x \<in> carrier \<Y> \<Longrightarrow> \<pi>\<^sub>* x = \<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* x))"
    by (metis upper_comp)

  theorem lower_by_complete_lattice:
    assumes "complete_lattice \<Y>" "x \<in> carrier \<X>"
    shows "\<pi>\<^sup>*(x) = \<Sqinter>\<^bsub>\<Y>\<^esub> { y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>*(y) }"
  proof -
    interpret Y: complete_lattice \<Y>
      by (simp add: assms)

    show ?thesis
    proof (rule Y.le_antisym)
      show x: "\<pi>\<^sup>* x \<in> carrier \<Y>"
        using assms(2) lower_closure by blast
      show "\<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> \<Sqinter>\<^bsub>\<Y>\<^esub>{y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y}"
      proof (rule Y.weak.inf_greatest)
        show "{y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y} \<subseteq> carrier \<Y>"
          by auto
        show "\<pi>\<^sup>* x \<in> carrier \<Y>" by (fact x)
        fix z
        assume "z \<in> {y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y}" 
        thus "\<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> z"
          using assms(2) left by auto
      qed
      show "\<Sqinter>\<^bsub>\<Y>\<^esub>{y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y} \<sqsubseteq>\<^bsub>\<Y>\<^esub> \<pi>\<^sup>* x"
      proof (rule Y.weak.inf_lower)
        show "{y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y} \<subseteq> carrier \<Y>"
          by auto
        show "\<pi>\<^sup>* x \<in> {y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y}"
        proof (auto)
          show "\<pi>\<^sup>* x \<in> carrier \<Y>" by (fact x)
          show "x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* (\<pi>\<^sup>* x)"
            using assms(2) inflation by blast
        qed
      qed
      show "\<Sqinter>\<^bsub>\<Y>\<^esub>{y \<in> carrier \<Y>. x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y} \<in> carrier \<Y>"
       by (auto intro: Y.weak.inf_closed)
    qed
  qed

  theorem upper_by_complete_lattice:
    assumes "complete_lattice \<X>" "y \<in> carrier \<Y>"
    shows "\<pi>\<^sub>*(y) = \<Squnion>\<^bsub>\<X>\<^esub> { x \<in> carrier \<X>. \<pi>\<^sup>*(x) \<sqsubseteq>\<^bsub>\<Y>\<^esub> y }"
  proof -
    interpret X: complete_lattice \<X>
      by (simp add: assms)
    show ?thesis
    proof (rule X.le_antisym)
      show y: "\<pi>\<^sub>* y \<in> carrier \<X>"
        using assms(2) upper_closure by blast
      show "\<pi>\<^sub>* y \<sqsubseteq>\<^bsub>\<X>\<^esub> \<Squnion>\<^bsub>\<X>\<^esub>{x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y}"
      proof (rule X.weak.sup_upper)
        show "{x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y} \<subseteq> carrier \<X>"
          by auto
        show "\<pi>\<^sub>* y \<in> {x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y}"
        proof (auto)
          show "\<pi>\<^sub>* y \<in> carrier \<X>" by (fact y)
          show "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<sqsubseteq>\<^bsub>\<Y>\<^esub> y"
            by (simp add: assms(2) deflation)
        qed
      qed
      show "\<Squnion>\<^bsub>\<X>\<^esub>{x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y} \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
      proof (rule X.weak.sup_least)
        show "{x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y} \<subseteq> carrier \<X>"
          by auto
        show "\<pi>\<^sub>* y \<in> carrier \<X>" by (fact y)
        fix z
        assume "z \<in> {x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y}" 
        thus "z \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
          by (simp add: assms(2) right)
      qed
      show "\<Squnion>\<^bsub>\<X>\<^esub>{x \<in> carrier \<X>. \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y} \<in> carrier \<X>"
       by (auto intro: X.weak.sup_closed)
    qed
  qed

  lemma 
    assumes "complete_lattice \<X>" "complete_lattice \<Y>" "X \<subseteq> carrier \<X>"
    shows "\<pi>\<^sup>*(\<Squnion>\<^bsub>\<X>\<^esub> X) = \<Squnion>\<^bsub>\<Y>\<^esub> {\<pi>\<^sup>*(x) | x. x \<in> X}"
    oops (* TODO *)

end

lemma dual_galois [simp]: " galois_connection \<lparr> orderA = inv_gorder B, orderB = inv_gorder A, lower = f, upper = g \<rparr> 
                          = galois_connection \<lparr> orderA = A, orderB = B, lower = g, upper = f \<rparr>"
  by (auto simp add: galois_connection_def galois_connection_axioms_def connection_def dual_order_iff)

definition lower_adjoint :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "lower_adjoint A B f \<equiv> \<exists>g. galois_connection \<lparr> orderA = A, orderB = B, lower = f, upper = g \<rparr>"

definition upper_adjoint :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upper_adjoint A B g \<equiv> \<exists>f. galois_connection \<lparr> orderA = A, orderB = B, lower = f, upper = g \<rparr>"

lemma lower_adjoint_dual [simp]: "lower_adjoint (inv_gorder A) (inv_gorder B) f = upper_adjoint B A f"
  by (simp add: lower_adjoint_def upper_adjoint_def)

lemma upper_adjoint_dual [simp]: "upper_adjoint (inv_gorder A) (inv_gorder B) f = lower_adjoint B A f"
  by (simp add: lower_adjoint_def upper_adjoint_def)

lemma lower_type: "lower_adjoint A B f \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier B"
  by (auto simp add:lower_adjoint_def galois_connection_def galois_connection_axioms_def connection_def)

lemma upper_type: "upper_adjoint A B g \<Longrightarrow> g \<in> carrier B \<rightarrow> carrier A"
  by (auto simp add:upper_adjoint_def galois_connection_def galois_connection_axioms_def connection_def)

lemma id_galois: "partial_order A \<Longrightarrow> galois_connection (I\<^sub>g(A))"
  by (simp add: id_galcon_def galois_connection_def galois_connection_axioms_def connection_def)

lemma comp_galcon_closed:
  assumes "galois_connection G" "galois_connection F" "\<Y>\<^bsub>F\<^esub> = \<X>\<^bsub>G\<^esub>"
  shows "galois_connection (G \<circ>\<^sub>g F)"
proof -
  interpret F: galois_connection F
    by (simp add: assms)
  interpret G: galois_connection G
    by (simp add: assms)
  
  have "partial_order \<X>\<^bsub>G \<circ>\<^sub>g F\<^esub>"
    by (simp add: F.is_order_A comp_galcon_def)
  moreover have "partial_order \<Y>\<^bsub>G \<circ>\<^sub>g F\<^esub>"
    by (simp add: G.is_order_B comp_galcon_def)
  moreover have "\<pi>\<^sup>*\<^bsub>G\<^esub> \<circ> \<pi>\<^sup>*\<^bsub>F\<^esub> \<in> carrier \<X>\<^bsub>F\<^esub> \<rightarrow> carrier \<Y>\<^bsub>G\<^esub>"
    using F.lower_closure G.lower_closure assms(3) by auto
  moreover have "\<pi>\<^sub>*\<^bsub>F\<^esub> \<circ> \<pi>\<^sub>*\<^bsub>G\<^esub> \<in> carrier \<Y>\<^bsub>G\<^esub> \<rightarrow> carrier \<X>\<^bsub>F\<^esub>"
    using F.upper_closure G.upper_closure assms(3) by auto
  moreover 
  have "\<And> x y. \<lbrakk>x \<in> carrier \<X>\<^bsub>F\<^esub>; y \<in> carrier \<Y>\<^bsub>G\<^esub> \<rbrakk> \<Longrightarrow> 
               (\<pi>\<^sup>*\<^bsub>G\<^esub> (\<pi>\<^sup>*\<^bsub>F\<^esub> x) \<sqsubseteq>\<^bsub>\<Y>\<^bsub>G\<^esub>\<^esub> y) = (x \<sqsubseteq>\<^bsub>\<X>\<^bsub>F\<^esub>\<^esub> \<pi>\<^sub>*\<^bsub>F\<^esub> (\<pi>\<^sub>*\<^bsub>G\<^esub> y))"
    by (metis F.galois_property F.lower_closure G.galois_property G.upper_closure assms(3) Pi_iff)
  ultimately show ?thesis
    by (simp add: comp_galcon_def galois_connection_def galois_connection_axioms_def connection_def)
qed

lemma comp_galcon_right_unit [simp]: "F \<circ>\<^sub>g I\<^sub>g(\<X>\<^bsub>F\<^esub>) = F"
  by (simp add: comp_galcon_def id_galcon_def)

lemma comp_galcon_left_unit [simp]: "I\<^sub>g(\<Y>\<^bsub>F\<^esub>) \<circ>\<^sub>g F = F"
  by (simp add: comp_galcon_def id_galcon_def)

lemma galois_connectionI:
  assumes
    "partial_order A" "partial_order B"
    "L \<in> carrier A \<rightarrow> carrier B" "R \<in> carrier B \<rightarrow> carrier A"
    "isotone A B L" "isotone B A R" 
    "\<And> x y. \<lbrakk> x \<in> carrier A; y \<in> carrier B \<rbrakk> \<Longrightarrow> L x \<sqsubseteq>\<^bsub>B\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> R y"
  shows "galois_connection \<lparr> orderA = A, orderB = B, lower = L, upper = R \<rparr>"
  using assms by (simp add: galois_connection_def connection_def galois_connection_axioms_def)

lemma galois_connectionI':
  assumes
    "partial_order A" "partial_order B"
    "L \<in> carrier A \<rightarrow> carrier B" "R \<in> carrier B \<rightarrow> carrier A"
    "isotone A B L" "isotone B A R" 
    "\<forall> X \<in> carrier(B). L(R(X)) \<sqsubseteq>\<^bsub>B\<^esub> X"
    "\<forall> X \<in> carrier(A). X \<sqsubseteq>\<^bsub>A\<^esub> R(L(X))"
  shows "galois_connection \<lparr> orderA = A, orderB = B, lower = L, upper = R \<rparr>"
  using assms
  by (auto simp add: galois_connection_def connection_def galois_connection_axioms_def, (meson PiE isotone_def weak_partial_order.le_trans)+)

locale retract = galois_connection +
  assumes retract_property: "x \<in> carrier \<X> \<Longrightarrow> \<pi>\<^sub>* (\<pi>\<^sup>* x) \<sqsubseteq>\<^bsub>\<X>\<^esub> x"
begin
  lemma retract_inverse: "x \<in> carrier \<X> \<Longrightarrow> \<pi>\<^sub>* (\<pi>\<^sup>* x) = x"
    by (meson funcset_mem inflation is_order_A lower_closure partial_order.le_antisym retract_axioms retract_axioms_def retract_def upper_closure)

  lemma retract_injective: "inj_on \<pi>\<^sup>* (carrier \<X>)"
    by (metis inj_onI retract_inverse)
end  

locale coretract = galois_connection +
  assumes coretract_property: "y \<in> carrier \<Y> \<Longrightarrow> y \<sqsubseteq>\<^bsub>\<Y>\<^esub> \<pi>\<^sup>* (\<pi>\<^sub>* y)"
begin
  lemma coretract_inverse: "y \<in> carrier \<Y> \<Longrightarrow> \<pi>\<^sup>* (\<pi>\<^sub>* y) = y"
    by (meson coretract_axioms coretract_axioms_def coretract_def deflation funcset_mem is_order_B lower_closure partial_order.le_antisym upper_closure)
 
  lemma retract_injective: "inj_on \<pi>\<^sub>* (carrier \<Y>)"
    by (metis coretract_inverse inj_onI)
end  

end
