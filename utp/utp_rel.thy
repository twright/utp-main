section {* Alphabetised Relations *}

theory utp_rel
imports
  utp_pred_laws
  utp_recursion
  utp_lift
  utp_tactics
begin

text {* An alphabetised relation is simply a predicate whose state-space is a product type. In this
  theory we construct the core operators of the relational calculus, and prove a libary of 
  associated theorems, based on Chapters 2 and 5 of the UTP book~\cite{Hoare&98}. *}
  
subsection {* Relational Alphabets *}
  
text {* We set up convenient syntax to refer to the input and output parts of the alphabet, as is
  common in UTP. Since we are in a product space, these are simply the lenses @{term "fst\<^sub>L"} and
  @{term "snd\<^sub>L"}. *}
  
definition in\<alpha> :: "('\<alpha> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in\<alpha> = fst\<^sub>L"

definition out\<alpha> :: "('\<beta> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out\<alpha> = snd\<^sub>L"

lemma in\<alpha>_uvar [simp]: "vwb_lens in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "vwb_lens out\<alpha>"
  by (unfold_locales, auto simp add: out\<alpha>_def)

lemma var_in_alpha [simp]: "x ;\<^sub>L in\<alpha> = ivar x"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma var_out_alpha [simp]: "x ;\<^sub>L out\<alpha> = ovar x"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma drop_pre_inv [simp]: "\<lbrakk> out\<alpha> \<sharp> p \<rbrakk> \<Longrightarrow> \<lceil>\<lfloor>p\<rfloor>\<^sub><\<rceil>\<^sub>< = p"
  by (pred_simp)

lemma usubst_lookup_ivar_unrest [usubst]:
  "in\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s (ivar x) = $x"
  by (rel_simp, metis fstI)

lemma usubst_lookup_ovar_unrest [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s (ovar x) = $x\<acute>"
  by (rel_simp, metis sndI)
    
lemma out_alpha_in_indep [simp]:
  "out\<alpha> \<bowtie> in_var x" "in_var x \<bowtie> out\<alpha>"
  by (simp_all add: in_var_def out\<alpha>_def lens_indep_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_alpha_out_indep [simp]:
  "in\<alpha> \<bowtie> out_var x" "out_var x \<bowtie> in\<alpha>"
  by (simp_all add: in_var_def in\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

text {* The following two functions lift a predicate substitution to a relational one. *}
    
abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"
    
text {* The alphabet of a relation then consists wholly of the input and output portions. *}

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (simp add: fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def)

subsection {* Relational Types and Operators *}

text {* We create type synonyms for conditions (which are simply predicates) -- i.e. relations
  without dashed variables --, alphabetised relations where the input and output alphabet can
  be different, and finally homogeneous relations. *}
  
type_synonym '\<alpha> cond      = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) rel = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrel      = "('\<alpha> \<times> '\<alpha>) upred"
  
translations
  (type) "('\<alpha>, '\<beta>) rel" <= (type) "('\<alpha> \<times> '\<beta>) upred"

text {* We set up some overloaded constants for sequential composition and the identity in case
  we want to overload their definitions later. *}
  
consts
  useq   :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 71)
  uskip  :: "'a" ("II")
  
text {* We define a specialised version of the conditional where the condition can refer only to
  undashed variables, as is usually the case in programs, but not universally in UTP models. 
  We implement this by lifting the condition predicate into the relational state-space with
  construction @{term "\<lceil>b\<rceil>\<^sub><"}. *}
  
abbreviation 
  rcond :: "('\<alpha>, '\<beta>) rel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel"
  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
  where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"

text {* Sequential composition is heterogeneous, and simply requires that the output alphabet
  of the first matches then input alphabet of the second. We define it by lifting HOL's 
  built-in relational composition operator (@{term "op O"}). Since this returns a set, the
  definition states that the state binding $b$ is an element of this set. *}
  
lift_definition seqr::"('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<beta>, '\<gamma>) rel \<Rightarrow> ('\<alpha> \<times> '\<gamma>) upred"
is "\<lambda> P Q b. b \<in> ({p. P p} O {q. Q q})" .

adhoc_overloading
  useq seqr
   
text {* We also set up a homogeneous sequential composition operator, and versions of @{term true}
  and @{term false} that are explicitly typed by a homogeneous alphabet. *}

abbreviation seqh :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" (infixr ";;\<^sub>h" 71) where
"seqh P Q \<equiv> (P ;; Q)"

abbreviation truer :: "'\<alpha> hrel" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'\<alpha> hrel" ("false\<^sub>h") where
"falser \<equiv> false"
  
text {* We define the relational converse operator as an alphabet extrusion on the bijective
  lens @{term swap\<^sub>L} that swaps the elements of the product state-space. *}
    
abbreviation conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
where "conv_r e \<equiv> e \<oplus>\<^sub>p swap\<^sub>L"

text {* Assignment is defined using substitutions, where latter defines what each variable should
  map to. The definition of the operator identifies the after state binding, $b'$, with the 
  substitution function applied to the before state binding $b$. *}
  
lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^sub>a")
  is "\<lambda> \<sigma> (b, b'). b' = \<sigma>(b)" .

text {* Relational identity, or skip, is then simply an assignment with the identity substitution:
  it simply identifies all variables. *}
    
definition skip_r :: "'\<alpha> hrel" where
[urel_defs]: "skip_r = assigns_r id"

adhoc_overloading
  uskip skip_r

text {* We set up iterated sequential composition which iterates an indexed predicate over the
  elements of a list. *}
  
definition seqr_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
[urel_defs]: "seqr_iter xs P = foldr (\<lambda> i Q. P(i) ;; Q) xs II"
  
text {* A singleton assignment simply applies a singleton substitution function, and similarly
  for a double assignment. *}

abbreviation assign_r :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_r x v \<equiv> \<langle>[x \<mapsto>\<^sub>s v]\<rangle>\<^sub>a"

abbreviation assign_2_r ::
  "('t1 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t2 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

text {* We also define the alphabetised skip operator that identifies all input and output variables
  in the given alphabet lens. All other variables are unrestricted. We also set up syntax for it. *}
  
definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrel" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

text {* Similarly, we define the alphabetised assignment operator. *}

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> skip_ra a)"

text {* Assumptions ($c^{\top}$) and assertions ($c_{\bot}$) are encoded as conditionals. An assumption
  behaves like skip if the condition is true, and otherwise behaves like @{term false} (miracle).
  An assertion is the same, but yields @{term true}, which is an abort. *}

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<top>" [999] 999) where
[urel_defs]: "rassume c = II \<triangleleft> c \<triangleright>\<^sub>r false"

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sub>\<bottom>" [999] 999) where
[urel_defs]: "rassert c = II \<triangleleft> c \<triangleright>\<^sub>r true"

text {* A test is like a precondition, except that it identifies to the postcondition, and is thus
  a refinement of @{term II}. It forms the basis for Kleene Algebra with Tests~\cite{kozen1997kleene,Armstrong2015} 
  (KAT), which embeds a Boolean algebra into a Kleene algebra to represent conditions. *}

definition lift_test :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("\<lceil>_\<rceil>\<^sub>t")
where [urel_defs]: "\<lceil>b\<rceil>\<^sub>t = (\<lceil>b\<rceil>\<^sub>< \<and> II)"

text {* We define two variants of while loops based on strongest and weakest fixed points. The former
  is @{term false} for an infinite loop, and the latter is @{term true}. *}

definition while :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sup>\<top> _ do _ od") where
[urel_defs]: "while\<^sup>\<top> b do P od = (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

abbreviation while_top :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ do _ od") where
"while b do P od \<equiv> while\<^sup>\<top> b do P od"

definition while_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ do _ od") where
[urel_defs]: "while\<^sub>\<bottom> b do P od = (\<mu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

text {* While loops with invariant decoration (cf. \cite{Armstrong2015}). *}

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ invr _ do _ od") where
[urel_defs]: "while b invr p do S od = while b do S od"

text {* We implement a poor man's version of alphabet restriction that hides a variable within 
  a relation. *}

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
[urel_defs]: "P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

text {* We next describe frames and antiframes with the help of lenses. A frame states that $P$
  defines the behaviour of all variables not in $a$, and all those in $a$ remain the same. An
  antiframe describes the converse: all variables in $a$ are specified by $P$, and all other
  variables remain the same. For more information please see \cite{Morgan90a}.*}

definition frame :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "frame a P = (skip_ra a \<and> P)"

definition antiframe :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "antiframe a P = (II\<restriction>\<^sub>\<alpha>a \<and> P)"

subsection {* Syntax Translations *}
    
syntax
  -- {* Iterated sequential composition *}
  "_seqr_iter" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> '\<sigma> hrel \<Rightarrow> '\<sigma> hrel" ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)
  -- {* Single and multiple assignement *}
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":=" 72)
  -- {* Indexed assignment *}
  "_assignment_upd" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "[_] :=" 72)
  -- {* Substitution constructor *}
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"
  -- {* Alphabetised skip *}
  "_skip_ra"        :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")
  -- {* Frame *}
  "_frame"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:\<lbrakk>_\<rbrakk>" [64,0] 80)
  -- {* Antiframe *}
  "_antiframe" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [64,0] 80)
  
translations
  ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST seqr_iter) l (\<lambda>x. P)"
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST assigns_r (_mk_usubst (CONST id) xs vs)"
  "x := v" <= "CONST assigns_r (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x := v" <= "CONST assigns_r (CONST subst_upd (CONST id) x v)"
  "x,y := u,v" <= "CONST assigns_r (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"
  -- {* Indexed assignment uses the overloaded collection update function \emph{uupd}. *}
  "x [k] := v" => "x := &x(k \<mapsto> v)\<^sub>u"
  "_skip_ra v" \<rightleftharpoons> "CONST skip_ra v"
  "_frame x P" \<rightleftharpoons> "CONST frame x P"
  "_antiframe x P" \<rightleftharpoons> "CONST antiframe x P" 
  
subsection {* Relation Properties *}
  
text {* We describe some properties of relations, including functional and injective relations. *}

definition ufunctional :: "('a, 'b) rel \<Rightarrow> bool"
where [urel_defs]: "ufunctional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"

definition uinj :: "('a, 'b) rel \<Rightarrow> bool"
where [urel_defs]: "uinj R \<longleftrightarrow> II \<sqsubseteq> R ;; R\<^sup>-"

-- {* Configuration for UTP tactics (see @{theory utp_tactics}). *}

update_uexpr_rep_eq_thms -- {* Reread @{text rep_eq} theorems. *}

subsection {* Unrestriction Laws *}

lemma unrest_iuvar [unrest]: "out\<alpha> \<sharp> $x"
  by (metis fst_snd_lens_indep lift_pre_var out\<alpha>_def unrest_aext_indep)

lemma unrest_ouvar [unrest]: "in\<alpha> \<sharp> $x\<acute>"
  by (metis in\<alpha>_def lift_post_var snd_fst_lens_indep unrest_aext_indep)

lemma unrest_semir_undash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x \<sharp> P"
  shows "$x \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_semir_dash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x\<acute> \<sharp> Q"
  shows "$x\<acute> \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_cond [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> b; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<triangleleft> b \<triangleright> Q"
  by (rel_auto)

lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; in\<alpha> \<sharp> (P :: ('a, ('\<alpha> \<times> '\<beta>)) uexpr) \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (rel_auto)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; out\<alpha> \<sharp> (P :: ('a, ('\<alpha> \<times> '\<beta>)) uexpr) \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (rel_auto)

lemma unrest_pre_out\<alpha> [unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def)

lemma unrest_post_in\<alpha> [unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def)

lemma unrest_pre_in_var [unrest]:
  "x \<sharp> p1 \<Longrightarrow> $x \<sharp> \<lceil>p1\<rceil>\<^sub><"
  by (transfer, simp)

lemma unrest_post_out_var [unrest]:
  "x \<sharp> p1 \<Longrightarrow> $x\<acute> \<sharp> \<lceil>p1\<rceil>\<^sub>>"
  by (transfer, simp)

lemma unrest_convr_out\<alpha> [unrest]:
  "in\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: lens_defs)

lemma unrest_convr_in\<alpha> [unrest]:
  "out\<alpha> \<sharp> p \<Longrightarrow> in\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: lens_defs)

lemma unrest_in_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_out_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

subsection {* Substitution laws *}

lemma subst_seq_left [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = (\<sigma> \<dagger> P) ;; Q"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

lemma subst_seq_right [usubst]:
  "in\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = P ;; (\<sigma> \<dagger> Q)"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

text {* The following laws support substitution in heterogeneous relations for polymorphically
  typed literal expressions. These cannot be supported more generically due to limitations
  in HOL's type system. The laws are presented in a slightly strange way so as to be as
  general as possible. *}

lemma bool_seqr_laws [usubst]:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$x\<acute>\<rbrakk>)"
    by (rel_auto)+

lemma zero_one_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>0/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>1/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>0/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>1/$x\<acute>\<rbrakk>)"
    by (rel_auto)+

lemma numeral_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>numeral n/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>numeral n/$x\<acute>\<rbrakk>)"
  by (rel_auto)+

lemma usubst_condr [usubst]:
  "\<sigma> \<dagger> (P \<triangleleft> b \<triangleright> Q) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> b \<triangleright> \<sigma> \<dagger> Q)"
  by (rel_auto)

lemma subst_skip_r [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> II = \<langle>\<lfloor>\<sigma>\<rfloor>\<^sub>s\<rangle>\<^sub>a"
  by (rel_simp, (metis (mono_tags, lifting) prod.sel(1) sndI surjective_pairing)+)

lemma usubst_upd_in_comp [usubst]:
  "\<sigma>(&in\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x \<mapsto>\<^sub>s v)"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma usubst_upd_out_comp [usubst]:
  "\<sigma>(&out\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x\<acute> \<mapsto>\<^sub>s v)"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma subst_lift_upd [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by (simp add: alpha usubst, simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma subst_drop_upd [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  by pred_simp

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by (metis apply_subst_ext fst_vwb_lens in\<alpha>_def)

lemma unrest_usubst_lift_in [unrest]:
  "x \<sharp> P \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by pred_simp

lemma unrest_usubst_lift_out [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "$x\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by pred_simp

subsection {* Alphabet laws *}

lemma aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright> Q) \<oplus>\<^sub>p a = ((P \<oplus>\<^sub>p a) \<triangleleft> (b \<oplus>\<^sub>p a) \<triangleright> (Q \<oplus>\<^sub>p a))"
  by (rel_auto)

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_simp, metis wb_lens_weak weak_lens.put_get)

subsection {* Relational unrestriction *}

text {* Relational unrestriction states that a variable is unchanged by a relation. Eventually
  I'd also like to have it state that the relation also does not depend on the variable's
  initial value, but I'm not sure how to state that yet. For now we represent this by
  the parametric healthiness condition RID. *}

definition RID :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"
where "RID x P = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x)"

declare RID_def [urel_defs]

lemma RID_idem:
  "mwb_lens x \<Longrightarrow> RID(x)(RID(x)(P)) = RID(x)(P)"
  by (rel_auto)

lemma RID_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RID(x)(P) \<sqsubseteq> RID(x)(Q)"
  by (rel_auto)

lemma RID_skip_r:
  "vwb_lens x \<Longrightarrow> RID(x)(II) = II"
  apply (rel_auto) using vwb_lens.put_eq by fastforce

lemma RID_disj:
  "RID(x)(P \<or> Q) = (RID(x)(P) \<or> RID(x)(Q))"
  by (rel_auto)

lemma RID_conj:
  "vwb_lens x \<Longrightarrow> RID(x)(RID(x)(P) \<and> RID(x)(Q)) = (RID(x)(P) \<and> RID(x)(Q))"
  by (rel_auto)

lemma RID_assigns_r_diff:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> RID(x)(\<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_auto)
  apply (metis vwb_lens.put_eq)
  apply (metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
done

lemma RID_assign_r_same:
  "vwb_lens x \<Longrightarrow> RID(x)(x := v) = II"
  apply (rel_auto)
  using vwb_lens.put_eq apply fastforce
done

lemma RID_seq_left:
  assumes "vwb_lens x"
  shows "RID(x)(RID(x)(P) ;; Q) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(RID(x)(P) ;; Q) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> (\<exists> $x \<bullet> $x\<acute> =\<^sub>u $x)) ;; (\<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RID_seq_right:
  assumes "vwb_lens x"
  shows "RID(x)(P ;; RID(x)(Q)) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(P ;; RID(x)(Q)) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = (((\<exists> $x \<bullet>  P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> (\<exists> $x\<acute> \<bullet> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp robust, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

definition unrest_relation :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> bool" (infix "\<sharp>\<sharp>" 20)
where "(x \<sharp>\<sharp> P) \<longleftrightarrow> (P = RID(x)(P))"

declare unrest_relation_def [urel_defs]

lemma skip_r_runrest [unrest]:
  "vwb_lens x \<Longrightarrow> x \<sharp>\<sharp> II"
  by (simp add: RID_skip_r unrest_relation_def)

lemma assigns_r_runrest:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: RID_assigns_r_diff unrest_relation_def)

lemma seq_r_runrest [unrest]:
  assumes "vwb_lens x" "x \<sharp>\<sharp> P" "x \<sharp>\<sharp> Q"
  shows "x \<sharp>\<sharp> (P ;; Q)"
  by (metis RID_seq_left assms unrest_relation_def)

lemma false_runrest [unrest]: "x \<sharp>\<sharp> false"
  by (rel_auto)

lemma and_runrest [unrest]: "\<lbrakk> vwb_lens x; x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<and> Q)"
  by (metis RID_conj unrest_relation_def)

lemma or_runrest [unrest]: "\<lbrakk> x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<or> Q)"
  by (simp add: RID_disj unrest_relation_def)

subsection {* Relational alphabet extension *}

lift_definition rel_alpha_ext :: "'\<beta> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<oplus>\<^sub>R" 65)
is "\<lambda> P x (b1, b2). P (get\<^bsub>x\<^esub> b1, get\<^bsub>x\<^esub> b2) \<and> (\<forall> b. b1 \<oplus>\<^sub>L b on x = b2 \<oplus>\<^sub>L b on x)" .

lemma rel_alpha_ext_alt_def:
  assumes "vwb_lens y" "x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L" "x \<bowtie> y"
  shows "P \<oplus>\<^sub>R x = (P \<oplus>\<^sub>p (x \<times>\<^sub>L x) \<and> $y\<acute> =\<^sub>u $y)"
  using assms
  apply (rel_auto robust, simp_all add: lens_override_def)
  apply (metis lens_indep_get lens_indep_sym)
  apply (metis vwb_lens_def wb_lens.get_put wb_lens_def weak_lens.put_get)
done
    
end