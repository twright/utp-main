theory Order
imports Congruence FuncSet
begin

section {* Orders and Lattices *}

subsection {* Partial Orders *}

record 'a gorder = "'a eq_object" +
  le :: "['a, 'a] => bool" (infixl "\<sqsubseteq>\<index>" 50)

abbreviation inv_gorder :: "_ \<Rightarrow> 'a gorder" where
  "inv_gorder L \<equiv> \<lparr> carrier = carrier L
                  , eq = op .=\<^bsub>L\<^esub>
                  , le = (\<lambda> x y. y \<sqsubseteq>\<^bsub>L \<^esub>x) \<rparr>"

lemma inv_gorder_inv:
  "inv_gorder (inv_gorder L) = L"
  by simp

locale weak_partial_order = equivalence L for L (structure) +
  assumes le_refl [intro, simp]:
      "x \<in> carrier L ==> x \<sqsubseteq> x"
    and weak_le_antisym [intro]:
      "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L |] ==> x .= y"
    and le_trans [trans]:
      "[| x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L |] ==> x \<sqsubseteq> z"
    and le_cong:
      "\<lbrakk> x .= y; z .= w; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L; w \<in> carrier L \<rbrakk> \<Longrightarrow>
      x \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> w"

definition
  lless :: "[_, 'a, 'a] => bool" (infixl "\<sqsubset>\<index>" 50)
  where "x \<sqsubset>\<^bsub>L\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> y & x .\<noteq>\<^bsub>L\<^esub> y"

subsubsection {* The order relation *}

lemma funcset_carrier:
  "\<lbrakk> f \<in> carrier X \<rightarrow> carrier Y; x \<in> carrier X \<rbrakk> \<Longrightarrow> f x \<in> carrier Y"
  by (fact funcset_mem)

lemma funcset_carrier':
  "\<lbrakk> f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A \<rbrakk> \<Longrightarrow> f x \<in> carrier A"
  by (fact funcset_mem)

context weak_partial_order
begin

lemma le_cong_l [intro, trans]:
  "\<lbrakk> x .= y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD2])

lemma le_cong_r [intro, trans]:
  "\<lbrakk> x \<sqsubseteq> y; y .= z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD1])

lemma weak_refl [intro, simp]: "\<lbrakk> x .= y; x \<in> carrier L; y \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: le_cong_l)

end

lemma weak_llessI:
  fixes R (structure)
  assumes "x \<sqsubseteq> y" and "~(x .= y)"
  shows "x \<sqsubset> y"
  using assms unfolding lless_def by simp

lemma lless_imp_le:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "x \<sqsubseteq> y"
  using assms unfolding lless_def by simp

lemma weak_lless_imp_not_eq:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "\<not> (x .= y)"
  using assms unfolding lless_def by simp

lemma weak_llessE:
  fixes R (structure)
  assumes p: "x \<sqsubset> y" and e: "\<lbrakk>x \<sqsubseteq> y; \<not> (x .= y)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using p by (blast dest: lless_imp_le weak_lless_imp_not_eq e)

lemma (in weak_partial_order) lless_cong_l [trans]:
  assumes xx': "x .= x'"
    and xy: "x' \<sqsubset> y"
    and carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubset> y"
  using assms unfolding lless_def by (auto intro: trans sym)

lemma (in weak_partial_order) lless_cong_r [trans]:
  assumes xy: "x \<sqsubset> y"
    and  yy': "y .= y'"
    and carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
  shows "x \<sqsubset> y'"
  using assms unfolding lless_def by (auto intro: trans sym)  (*slow*)


lemma (in weak_partial_order) lless_antisym:
  assumes "a \<in> carrier L" "b \<in> carrier L"
    and "a \<sqsubset> b" "b \<sqsubset> a"
  shows "P"
  using assms
  by (elim weak_llessE) auto

lemma (in weak_partial_order) lless_trans [trans]:
  assumes "a \<sqsubset> b" "b \<sqsubset> c"
    and carr[simp]: "a \<in> carrier L" "b \<in> carrier L" "c \<in> carrier L"
  shows "a \<sqsubset> c"
  using assms unfolding lless_def by (blast dest: le_trans intro: sym)


subsubsection {* Upper and lower bounds of a set *}

definition
  Upper :: "[_, 'a set] => 'a set"
  where "Upper L A = {u. (ALL x. x \<in> A \<inter> carrier L --> x \<sqsubseteq>\<^bsub>L\<^esub> u)} \<inter> carrier L"

definition
  Lower :: "[_, 'a set] => 'a set"
  where "Lower L A = {l. (ALL x. x \<in> A \<inter> carrier L --> l \<sqsubseteq>\<^bsub>L\<^esub> x)} \<inter> carrier L"

lemma Upper_closed [intro!, simp]:
  "Upper L A \<subseteq> carrier L"
  by (unfold Upper_def) clarify

lemma Upper_memD [dest]:
  fixes L (structure)
  shows "[| u \<in> Upper L A; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u \<and> u \<in> carrier L"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_elemD [dest]:
  "[| u .\<in> Upper L A; u \<in> carrier L; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u"
  unfolding Upper_def elem_def
  by (blast dest: sym)

lemma Upper_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x \<in> Upper L A"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_elemI:
  "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x .\<in> Upper L A"
  unfolding Upper_def by blast

lemma Upper_antimono:
  "A \<subseteq> B ==> Upper L B \<subseteq> Upper L A"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_is_closed [simp]:
  "A \<subseteq> carrier L ==> is_closed (Upper L A)"
  by (rule is_closedI) (blast intro: Upper_memI)+

lemma (in weak_partial_order) Upper_mem_cong:
  assumes a'carr: "a' \<in> carrier L" and Acarr: "A \<subseteq> carrier L"
    and aa': "a .= a'"
    and aelem: "a \<in> Upper L A"
  shows "a' \<in> Upper L A"
proof (rule Upper_memI[OF _ a'carr])
  fix y
  assume yA: "y \<in> A"
  hence "y \<sqsubseteq> a" by (intro Upper_memD[OF aelem, THEN conjunct1] Acarr)
  also note aa'
  finally
      show "y \<sqsubseteq> a'"
      by (simp add: a'carr subsetD[OF Acarr yA] subsetD[OF Upper_closed aelem])
qed

lemma (in weak_partial_order) Upper_cong:
  assumes Acarr: "A \<subseteq> carrier L" and A'carr: "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "Upper L A = Upper L A'"
unfolding Upper_def
apply rule
 apply (rule, clarsimp) defer 1
 apply (rule, clarsimp) defer 1
proof -
  fix x a'
  assume carr: "x \<in> carrier L" "a' \<in> carrier L"
    and a'A': "a' \<in> A'"
  assume aLxCond[rule_format]: "\<forall>a. a \<in> A \<and> a \<in> carrier L \<longrightarrow> a \<sqsubseteq> x"

  from AA' and a'A' have "\<exists>a\<in>A. a' .= a" by (rule set_eqD2)
  from this obtain a
      where aA: "a \<in> A"
      and a'a: "a' .= a"
      by auto
  note [simp] = subsetD[OF Acarr aA] carr

  note a'a
  also have "a \<sqsubseteq> x" by (simp add: aLxCond aA)
  finally show "a' \<sqsubseteq> x" by simp
next
  fix x a
  assume carr: "x \<in> carrier L" "a \<in> carrier L"
    and aA: "a \<in> A"
  assume a'LxCond[rule_format]: "\<forall>a'. a' \<in> A' \<and> a' \<in> carrier L \<longrightarrow> a' \<sqsubseteq> x"

  from AA' and aA have "\<exists>a'\<in>A'. a .= a'" by (rule set_eqD1)
  from this obtain a'
      where a'A': "a' \<in> A'"
      and aa': "a .= a'"
      by auto
  note [simp] = subsetD[OF A'carr a'A'] carr

  note aa'
  also have "a' \<sqsubseteq> x" by (simp add: a'LxCond a'A')
  finally show "a \<sqsubseteq> x" by simp
qed

lemma Lower_closed [intro!, simp]:
  "Lower L A \<subseteq> carrier L"
  by (unfold Lower_def) clarify

lemma Lower_memD [dest]:
  fixes L (structure)
  shows "[| l \<in> Lower L A; x \<in> A; A \<subseteq> carrier L |] ==> l \<sqsubseteq> x \<and> l \<in> carrier L"
  by (unfold Lower_def) blast

lemma Lower_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> x \<sqsubseteq> y; x \<in> carrier L |] ==> x \<in> Lower L A"
  by (unfold Lower_def) blast

lemma Lower_antimono:
  "A \<subseteq> B ==> Lower L B \<subseteq> Lower L A"
  by (unfold Lower_def) blast

lemma (in weak_partial_order) Lower_is_closed [simp]:
  "A \<subseteq> carrier L \<Longrightarrow> is_closed (Lower L A)"
  by (rule is_closedI) (blast intro: Lower_memI dest: sym)+

lemma (in weak_partial_order) Lower_mem_cong:
  assumes a'carr: "a' \<in> carrier L" and Acarr: "A \<subseteq> carrier L"
    and aa': "a .= a'"
    and aelem: "a \<in> Lower L A"
  shows "a' \<in> Lower L A"
using assms Lower_closed[of L A]
by (intro Lower_memI) (blast intro: le_cong_l[OF aa'[symmetric]])

lemma (in weak_partial_order) Lower_cong:
  assumes Acarr: "A \<subseteq> carrier L" and A'carr: "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "Lower L A = Lower L A'"
unfolding Lower_def
apply rule
 apply clarsimp defer 1
 apply clarsimp defer 1
proof -
  fix x a'
  assume carr: "x \<in> carrier L" "a' \<in> carrier L"
    and a'A': "a' \<in> A'"
  assume "\<forall>a. a \<in> A \<and> a \<in> carrier L \<longrightarrow> x \<sqsubseteq> a"
  hence aLxCond: "\<And>a. \<lbrakk>a \<in> A; a \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> a" by fast

  from AA' and a'A' have "\<exists>a\<in>A. a' .= a" by (rule set_eqD2)
  from this obtain a
      where aA: "a \<in> A"
      and a'a: "a' .= a"
      by auto

  from aA and subsetD[OF Acarr aA]
      have "x \<sqsubseteq> a" by (rule aLxCond)
  also note a'a[symmetric]
  finally
      show "x \<sqsubseteq> a'" by (simp add: carr subsetD[OF Acarr aA])
next
  fix x a
  assume carr: "x \<in> carrier L" "a \<in> carrier L"
    and aA: "a \<in> A"
  assume "\<forall>a'. a' \<in> A' \<and> a' \<in> carrier L \<longrightarrow> x \<sqsubseteq> a'"
  hence a'LxCond: "\<And>a'. \<lbrakk>a' \<in> A'; a' \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> a'" by fast+

  from AA' and aA have "\<exists>a'\<in>A'. a .= a'" by (rule set_eqD1)
  from this obtain a'
      where a'A': "a' \<in> A'"
      and aa': "a .= a'"
      by auto
  from a'A' and subsetD[OF A'carr a'A']
      have "x \<sqsubseteq> a'" by (rule a'LxCond)
  also note aa'[symmetric]
  finally show "x \<sqsubseteq> a" by (simp add: carr subsetD[OF A'carr a'A'])
qed

text {* Jacobson: Theorem 8.1 *}

lemma Lower_empty [simp]:
  "Lower L {} = carrier L"
  by (unfold Lower_def) simp

lemma Upper_empty [simp]:
  "Upper L {} = carrier L"
  by (unfold Upper_def) simp

subsubsection {* Least and greatest, as predicate *}

definition
  least :: "[_, 'a, 'a set] => bool"
  where "least L l A \<longleftrightarrow> A \<subseteq> carrier L & l \<in> A & (ALL x : A. l \<sqsubseteq>\<^bsub>L\<^esub> x)"

definition
  greatest :: "[_, 'a, 'a set] => bool"
  where "greatest L g A \<longleftrightarrow> A \<subseteq> carrier L & g \<in> A & (ALL x : A. x \<sqsubseteq>\<^bsub>L\<^esub> g)"

text (in weak_partial_order) {* Could weaken these to @{term "l \<in> carrier L \<and> l
  .\<in> A"} and @{term "g \<in> carrier L \<and> g .\<in> A"}. *}

lemma least_closed [intro, simp]:
  "least L l A ==> l \<in> carrier L"
  by (unfold least_def) fast

lemma least_mem:
  "least L l A ==> l \<in> A"
  by (unfold least_def) fast

lemma (in weak_partial_order) weak_least_unique:
  "[| least L x A; least L y A |] ==> x .= y"
  by (unfold least_def) blast

lemma least_le:
  fixes L (structure)
  shows "[| least L x A; a \<in> A |] ==> x \<sqsubseteq> a"
  by (unfold least_def) fast

lemma (in weak_partial_order) least_cong:
  "[| x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A |] ==> least L x A = least L x' A"
  by (unfold least_def) (auto dest: sym)

abbreviation is_lub :: "[_, 'a, 'a set] => bool"
where "is_lub L x A \<equiv> least L x (Upper L A)"

text (in weak_partial_order) {* @{const least} is not congruent in the second parameter for 
  @{term "A {.=} A'"} *}

lemma (in weak_partial_order) least_Upper_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L"
  shows "least L x (Upper L A) = least L x' (Upper L A)"
  apply (rule least_cong) using assms by auto

lemma (in weak_partial_order) least_Upper_cong_r:
  assumes Acarrs: "A \<subseteq> carrier L" "A' \<subseteq> carrier L" (* unneccessary with current Upper? *)
    and AA': "A {.=} A'"
  shows "least L x (Upper L A) = least L x (Upper L A')"
apply (subgoal_tac "Upper L A = Upper L A'", simp)
by (rule Upper_cong) fact+

lemma least_UpperI:
  fixes L (structure)
  assumes above: "!! x. x \<in> A ==> x \<sqsubseteq> s"
    and below: "!! y. y \<in> Upper L A ==> s \<sqsubseteq> y"
    and L: "A \<subseteq> carrier L"  "s \<in> carrier L"
  shows "least L s (Upper L A)"
proof -
  have "Upper L A \<subseteq> carrier L" by simp
  moreover from above L have "s \<in> Upper L A" by (simp add: Upper_def)
  moreover from below have "ALL x : Upper L A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: least_def)
qed

lemma least_Upper_above:
  fixes L (structure)
  shows "[| least L s (Upper L A); x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> s"
  by (unfold least_def) blast

lemma greatest_closed [intro, simp]:
  "greatest L l A ==> l \<in> carrier L"
  by (unfold greatest_def) fast

lemma greatest_mem:
  "greatest L l A ==> l \<in> A"
  by (unfold greatest_def) fast

lemma (in weak_partial_order) weak_greatest_unique:
  "[| greatest L x A; greatest L y A |] ==> x .= y"
  by (unfold greatest_def) blast

lemma greatest_le:
  fixes L (structure)
  shows "[| greatest L x A; a \<in> A |] ==> a \<sqsubseteq> x"
  by (unfold greatest_def) fast

lemma (in weak_partial_order) greatest_cong:
  "[| x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A |] ==>
  greatest L x A = greatest L x' A"
  by (unfold greatest_def) (auto dest: sym)

abbreviation is_glb :: "[_, 'a, 'a set] => bool"
where "is_glb L x A \<equiv> greatest L x (Lower L A)"

text (in weak_partial_order) {* @{const greatest} is not congruent in the second parameter for 
  @{term "A {.=} A'"} *}

lemma (in weak_partial_order) greatest_Lower_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L" (* unneccessary with current Lower *)
  shows "greatest L x (Lower L A) = greatest L x' (Lower L A)"
  apply (rule greatest_cong) using assms by auto

lemma (in weak_partial_order) greatest_Lower_cong_r:
  assumes Acarrs: "A \<subseteq> carrier L" "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "greatest L x (Lower L A) = greatest L x (Lower L A')"
apply (subgoal_tac "Lower L A = Lower L A'", simp)
by (rule Lower_cong) fact+

lemma greatest_LowerI:
  fixes L (structure)
  assumes below: "!! x. x \<in> A ==> i \<sqsubseteq> x"
    and above: "!! y. y \<in> Lower L A ==> y \<sqsubseteq> i"
    and L: "A \<subseteq> carrier L"  "i \<in> carrier L"
  shows "greatest L i (Lower L A)"
proof -
  have "Lower L A \<subseteq> carrier L" by simp
  moreover from below L have "i \<in> Lower L A" by (simp add: Lower_def)
  moreover from above have "ALL x : Lower L A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: greatest_def)
qed

lemma greatest_Lower_below:
  fixes L (structure)
  shows "[| greatest L i (Lower L A); x \<in> A; A \<subseteq> carrier L |] ==> i \<sqsubseteq> x"
  by (unfold greatest_def) blast

lemma Lower_dual [simp]:
  "Lower (inv_gorder L) A = Upper L A"
  by (simp add:Upper_def Lower_def)

lemma Upper_dual [simp]:
  "Upper (inv_gorder L) A = Lower L A"
  by (simp add:Upper_def Lower_def)

lemma least_dual [simp]:
  "least (inv_gorder L) x A = greatest L x A"
  by (simp add:least_def greatest_def)

lemma greatest_dual [simp]:
  "greatest (inv_gorder L) x A = least L x A"
  by (simp add:least_def greatest_def)

lemma (in weak_partial_order) dual_weak_order:
  "weak_partial_order (inv_gorder L)"
  apply (unfold_locales)
  apply (simp_all)
  apply (metis sym)
  apply (metis trans)
  apply (metis weak_le_antisym)
  apply (metis le_trans)
  apply (metis le_cong_l le_cong_r sym)
done

lemma dual_weak_order_iff:
  "weak_partial_order (inv_gorder A) \<longleftrightarrow> weak_partial_order A"
proof
  assume "weak_partial_order (inv_gorder A)"
  then interpret dpo: weak_partial_order "inv_gorder A"
  rewrites "carrier (inv_gorder A) = carrier A"
  and   "le (inv_gorder A)      = (\<lambda> x y. le A y x)"
  and   "eq (inv_gorder A)      = eq A"
    by (simp_all)
  show "weak_partial_order A"
    by (unfold_locales, auto intro: dpo.sym dpo.trans dpo.le_trans)
next
  assume "weak_partial_order A"
  thus "weak_partial_order (inv_gorder A)"
    by (metis weak_partial_order.dual_weak_order)
qed

subsubsection {* Intervals *}

definition
  at_least_at_most :: "('a, 'c) gorder_scheme \<Rightarrow> 'a => 'a => 'a set" ("(1\<lbrace>_.._\<rbrace>\<index>)") where
  "\<lbrace>l..u\<rbrace>\<^bsub>A\<^esub> = {x \<in> carrier A. l \<sqsubseteq>\<^bsub>A\<^esub> x \<and> x \<sqsubseteq>\<^bsub>A\<^esub> u}"

subsubsection {* Isotone functions *}

definition isotone :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "isotone A B f \<equiv> weak_partial_order A 
                 \<and> weak_partial_order B 
                 \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y)"

lemma isotoneI [intro?]:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "weak_partial_order L1"
          "weak_partial_order L2"
          "(\<And>x y. \<lbrakk> x \<in> carrier L1; y \<in> carrier L1; x \<sqsubseteq>\<^bsub>L1\<^esub> y \<rbrakk> 
                   \<Longrightarrow> f x \<sqsubseteq>\<^bsub>L2\<^esub> f y)"
  shows "isotone L1 L2 f"
  using assms by (auto simp add:isotone_def)

abbreviation Monotone :: "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" ("Mono\<index>") where
"Monotone L f \<equiv> isotone L L f"

lemma use_iso1: "\<lbrakk>isotone A A f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>A\<^esub> f y"
  by (simp add: isotone_def)

lemma use_iso2: "\<lbrakk>isotone A B f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
  by (simp add: isotone_def)

lemma iso_compose: "\<lbrakk>f \<in> carrier A \<rightarrow> carrier B; isotone A B f; g \<in> carrier B \<rightarrow> carrier C; isotone B C g\<rbrakk> \<Longrightarrow> isotone A C (g \<circ> f)"
  by (simp add: isotone_def, safe, metis Pi_iff)

lemma (in weak_partial_order) inv_isotone [simp]: 
  "isotone (inv_gorder A) (inv_gorder B) f = isotone A B f"
  by (auto simp add:isotone_def dual_weak_order dual_weak_order_iff)

subsubsection {* Idempotent functions *}

definition idempotent :: 
  "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" ("Idem\<index>") where
"idempotent L f \<equiv> \<forall>x\<in>carrier L. f (f x) .=\<^bsub>L\<^esub> f x"

lemma (in weak_partial_order) idempotent:
  "\<lbrakk> Idem f; x \<in> carrier L \<rbrakk> \<Longrightarrow> f (f x) .= f x"
  by (auto simp add: idempotent_def)

subsubsection {* Order embeddings *}

definition order_emb :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "order_emb A B f \<equiv> weak_partial_order A 
                   \<and> weak_partial_order B 
                   \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. f x \<sqsubseteq>\<^bsub>B\<^esub> f y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y )"

lemma order_emb_isotone: "order_emb A B f \<Longrightarrow> isotone A B f"
  by (auto simp add: isotone_def order_emb_def)

definition commuting :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"commuting A f g = (\<forall>x\<in>A. (f \<circ> g) x = (g \<circ> f) x)"

subsection {* Orders and Lattices where @{text eq} is the Equality *}

locale partial_order = weak_partial_order +
  assumes eq_is_equal: "op .= = op ="
begin

declare weak_le_antisym [rule del]

lemma le_antisym [intro]:
  "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L |] ==> x = y"
  using weak_le_antisym unfolding eq_is_equal .

lemma lless_eq:
  "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y & x \<noteq> y"
  unfolding lless_def by (simp add: eq_is_equal)

lemma lless_asym:
  assumes "a \<in> carrier L" "b \<in> carrier L"
    and "a \<sqsubset> b" "b \<sqsubset> a"
  shows "P"
  using assms unfolding lless_eq by auto

lemma set_eq_is_eq: "A {.=} B \<longleftrightarrow> A = B"
  by (auto simp add: set_eq_def elem_def eq_is_equal)

end

lemma (in partial_order) dual_order:
  "partial_order (inv_gorder L)"
proof -
  interpret dwo: weak_partial_order "inv_gorder L"
    by (metis dual_weak_order)
  show ?thesis
    by (unfold_locales, simp add:eq_is_equal)
qed

lemma dual_order_iff:
  "partial_order (inv_gorder A) \<longleftrightarrow> partial_order A"
proof
  assume assm:"partial_order (inv_gorder A)"
  then interpret po: partial_order "inv_gorder A"
  rewrites "carrier (inv_gorder A) = carrier A"
  and   "le (inv_gorder A)      = (\<lambda> x y. le A y x)"
  and   "eq (inv_gorder A)      = eq A"
    by (simp_all)
  show "partial_order A"
    apply (unfold_locales, simp_all)
    apply (metis po.sym, metis po.trans)
    apply (metis po.weak_le_antisym, metis po.le_trans)
    apply (metis (full_types) po.eq_is_equal, metis po.eq_is_equal)
  done
next
  assume "partial_order A"
  thus "partial_order (inv_gorder A)"
    by (metis partial_order.dual_order)
qed

text {* Least and greatest, as predicate *}

lemma (in partial_order) least_unique:
  "[| least L x A; least L y A |] ==> x = y"
  using weak_least_unique unfolding eq_is_equal .

lemma (in partial_order) greatest_unique:
  "[| greatest L x A; greatest L y A |] ==> x = y"
  using weak_greatest_unique unfolding eq_is_equal .

subsection {* Bounded Orders *}

definition
  atop :: "_ => 'a" ("\<top>\<index>")
  where "\<top>\<^bsub>L\<^esub> = (SOME x. greatest L x (carrier L))"

definition
  abottom :: "_ => 'a" ("\<bottom>\<index>")
  where "\<bottom>\<^bsub>L\<^esub> = (SOME x. least L x (carrier L))"

locale weak_partial_order_bottom = weak_partial_order L for L (structure) +
  assumes bottom_exists: "\<exists> x. least L x (carrier L)"
begin

lemma bottom_least: "least L \<bottom> (carrier L)"
proof -
  obtain x where "least L x (carrier L)"
    by (metis bottom_exists)

  thus ?thesis
    by (auto intro:someI2 simp add:abottom_def)
qed

lemma bottom_closed [simp, intro]:
  "\<bottom> \<in> carrier L"
  by (metis bottom_least least_mem)

lemma bottom_lower [simp, intro]:
  "x \<in> carrier L \<Longrightarrow> \<bottom> \<sqsubseteq> x"
  by (metis bottom_least least_le)

end

locale weak_partial_order_top = weak_partial_order L for L (structure) +
  assumes top_exists: "\<exists> x. greatest L x (carrier L)"
begin

lemma top_greatest: "greatest L \<top> (carrier L)"
proof -
  obtain x where "greatest L x (carrier L)"
    by (metis top_exists)

  thus ?thesis
    by (auto intro:someI2 simp add:atop_def)
qed

lemma top_closed [simp, intro]:
  "\<top> \<in> carrier L"
  by (metis greatest_mem top_greatest)

lemma top_higher [simp, intro]:
  "x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> \<top>"
  by (metis greatest_le top_greatest)

end

subsection {* Total Orders *}

locale weak_total_order = weak_partial_order +
  assumes total: "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

text {* Introduction rule: the usual definition of total order *}

lemma (in weak_partial_order) weak_total_orderI:
  assumes total: "!!x y. [| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "weak_total_order L"
  by default (rule total)

text {* Total Orders *}

locale total_order = partial_order +
  assumes total_order_total: "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

sublocale total_order < weak: weak_total_order
  by default (rule total_order_total)

text {* Introduction rule: the usual definition of total order *}

lemma (in partial_order) total_orderI:
  assumes total: "!!x y. [| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "total_order L"
  by default (rule total)

end