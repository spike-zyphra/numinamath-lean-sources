import Mathlib

open Real Polynomial

/- The different non-zero real numbers a, b, c satisfy the set equality $\{a + b, b + c, c + a\} = \{ab, bc, ca\}$.
Prove that the set equality $\{a, b, c\} = \{a^2 -2, b^2 - 2, c^2 - 2\}$ also holds.
.
(Josef Tkadlec) -/
theorem algebra_45176 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a ≠ b) (h2 : b ≠ c) (h3 : c ≠ a)
    (h4 : ({a + b, b + c, c + a} : Multiset ℝ) = {a * b, b * c, c * a}) :
    ({a, b, c} : Multiset ℝ) = {a ^ 2 - 2, b ^ 2 - 2, c ^ 2 - 2} := by
    -- Let $f(x) = x^3 - px^2 + qx - r$ be the monic polynomial with distinct roots $a, b, c$ . From Vieta's, $a + b + c = p, ab + bc + ca = q,$ and $abc = r$ . 
    let p := a + b + c
    let q := a * b + b * c + c * a
    let r := a * b * c
    let f := X ^ 3 - C p * X ^ 2 + C q * X - C r
    have hf1 : f.natDegree = 3 := by
      simp [f] ;compute_degree!
    have hf2 : Monic f := by 
      simp [f]
      refine Monic.def.mpr ?_
      rw [← Polynomial.coeff_natDegree,hf1]
      simp
    have hf3 : f.roots = {a,b,c} := by
      have : f = (X - C a) * (X - C b) * (X - C c) := by
        simp [f,p,q,r] ;ring_nf
      have this' : (X - C a) * (X - C b) ≠ 0 := by 
        refine Monic.mul_left_ne_zero ?_ ?_
        exact monic_X_sub_C b
        exact X_sub_C_ne_zero a
      rw [this,roots_mul,roots_mul] ;simp
      exact this'
      refine Monic.mul_left_ne_zero ?_ this'
      exact monic_X_sub_C c
    have hf4 : f.roots.card = f.natDegree := by
      rw [hf1,hf3] ;simp
    -- Since $\{a + b, b + c, c + a\} = \{ab, bc, ca\}$ , we have $(a + b) + (b + c) + (c + a) = ab + bc + ca \iff 2p = q$ ,\
    have h5 : ({a + b, b + c, c + a} : Multiset ℝ).esymm 1 = ({a * b, b * c, c * a} : Multiset ℝ).esymm 1 := by rw [h4]
    -- $(a + b)(b + c) + (b + c)(c + a) + (c + a)(a + b) = (ab)(bc) + (bc)(ca) + (ca)(ab) \iff (a + b + c)^2 + (ab + bc + ca) = abc(a + b + c)$\
    -- $\iff p^2 + q = pr \iff p(p - r + 2) = 0 \iff p = 0$ or $p = r - 2$ ,\
    have h6 : ({a + b, b + c, c + a} : Multiset ℝ).esymm 2 = ({a * b, b * c, c * a} : Multiset ℝ).esymm 2 := by rw [h4]
    -- --and $(a + b)(b + c)(c + a) = (ab)(bc)(ca) \iff (a + b + c)(ab + bc + ca) - abc = (abc)^2 \iff pq - r = r^2 \iff 2p^2 = r^2 + r$ .
    have h7 : ({a + b, b + c, c + a} : Multiset ℝ).esymm 3 = ({a * b, b * c, c * a} : Multiset ℝ).esymm 3 := by rw [h4]
    simp [Multiset.esymm, Multiset.powersetCard_one] at h5 h6 h7
    have h5' : 2 * p = q := by
      simp [p,q] ; linarith only [h5]
    have h6' : p = 0 ∨ (p - r + 2) = 0 := by
      have : p * (p - r + 2) = 0 := by
        simp only [p,r] ;linarith
      simp at this ;exact this
    have h7' : 2 * p ^ 2 = r ^ 2 + r := by
      rw [pow_two,← mul_assoc,h5'] 
      simp [p,q,r] ;linarith only [h7]
    -- If $p = 0$ , then $q =0$ and $r^2 + r = 0 \iff r = 0$ or $r = -1$ . So $f(x) = x^3$ or $x^3 + 1$ . But both of them do not have three distinct roots, contradiction.
    rcases h6' with hp | hp
    · simp [hp] at h5' h7'
      have hr : r = 0 ∨ r = -1 := by
        have : r ^ 2 + r = r * (r + 1) := by ring
        simp [← h7'] at this
        rcases this with this | this
        · left ;exact this
        right ;linarith
      rcases hr with hr | hr
      · simp only [f] at hf3
        rw [hp,← h5',hr] at hf3
        simp at hf3
        have : a = 0 := by
          have : a ∈ 3 • ({0}:Multiset ℝ) := by
            rw [hf3] ;simp
          simp at this
          exact this
        simp [this] at ha
      simp only [f] at hf3
      rw [hp,← h5',hr] at hf3
      simp at hf3
      have : ∀ (x:ℝ), x ∈ (X ^ 3 + 1).roots → x = -1 := by
        intro x hx
        have : (X ^ 3 + 1).eval x = 0 := by
          apply Polynomial.IsRoot.def.mp
          exact isRoot_of_mem_roots hx
        simp at this
        have : x ^ 3 = -1 := by linarith
        apply pow_eq_neg_one_iff.mp at this
        linarith
      have : a = -1 ∧ b = -1 := by
        constructor
        <;> apply this
        <;> simp [hf3]
      simp [this.1,this.2] at h1
    --  If $p = r - 2$ , then $2(r - 2)^2 = r^2 + r \iff r^2 - 9r + 8 = 0 \iff r = 1$ or $r = 8$ . 
    have hr : r = 8 ∨ r = 1 := by
      have : (r - 1) * (r - 8) = 0 := by
        have : p = r - 2 := by linarith only [hp]
        rw [this] at h7' 
        linarith only [h7']
      simp at this
      rcases this with this | this
      · right ;linarith only [this]
      left ;linarith only [this]
    --  If $r = 8$ , then $p = 6$ and $q = 12$ , giving us $f(x) = x^3 - 6x^2 + 12x - 8 = (x - 2)^3$ , which does not have three distinct roots.
    rcases hr with hr | hr
    · have hp' : p = 6 := by linarith
      have hq' : q = 12 := by linarith only [h5',hp']
      have hf5 : f = (X - C 2) ^ 3 := by
        simp [f,hp',hq',hr]
        ring_nf
        rw [← C_pow,mul_assoc, ← C_pow,mul_assoc]
        have : (3:ℝ[X]) = C (3 : ℝ) := rfl
        rw [this,← C_mul,← C_mul]
        norm_num
      have : ∀ (x:ℝ), x ∈ f.roots → x = 2 := by
        intro x hx
        have : f.eval x = 0 := by
          apply Polynomial.IsRoot.def.mp
          exact isRoot_of_mem_roots hx
        simp [hf5] at this
        linarith
      rw [hf3] at this
      have : a = 2 ∧ b = 2 := by
        constructor
        <;> apply this
        <;> simp
      simp [this.1,this.2] at h1
    -- So the only possible case is when $r = 1$ for which $p = -1, q = -2$ , and $f(x) = x^3 + x^2 - 2x - 1$ .
    have hp' : p = -1 := by linarith only [hr,hp]
    have hq' : q = -2 := by linarith only [hp' ,h5']
    have hf5 : f = X ^ 3 + X ^ 2 - C 2 * X - C 1 := by 
      simp [f,hr,hp',hq'] ;ring
    -- Now we will show that $f(a^2 - 2) = f(b^2 - 2) = f(c^2 - 2) = 0$ .\
    -- Notice that $f(x^2 - 2) = (x^2 - 2)^3 + (x^2 - 2)^2 - 2(x^2 - 2) - 1 = x^6 - 5x^4 + 6x^2 - 1$\
    -- $= (x^3 - 2x)^2 - (x^2 - 1)^2 =(x^3 + x^2 - 2x - 1)(x^3 - x^2 - 2x + 1) = f(x)(x^3 - x^2 - 2x + 1)$ . Thus, since $f(a) = f(b) = f(c) = 0$ , we have $f(a^2 - 2) = f(b^2 - 2) = f(c^2 - 2) = 0$ . 
    have hf6 : ∀ x ∈ f.roots, x^2-2 ∈ f.roots := by
      intro x hx
      have : f.eval x = 0 := by
        apply Polynomial.IsRoot.def.mp
        exact isRoot_of_mem_roots hx
      have : f.eval (x^2-2) = 0 := by
        have this' : f.eval (x^2-2) = (f.eval x) * (x^3-x^2-2*x+1) := by
          simp [hf5] ;ring_nf
        rw [this',this,zero_mul]
      apply (Polynomial.mem_roots ?_).mpr
      apply Polynomial.IsRoot.def.mpr this
      by_contra!
      have : f.eval 1 = 0 := by simp [this]
      simp [hf5] at this
      norm_num at this
    -- Therefore, $a^2 - 2, b^2 - 2, c^2 - 2$ are the roots of $f(x)$ and $\{a, b, c\} = \{a^2 - 2, b^2 - 2, c^2 - 2\}$ .
    have hf7 : {a^2 - 2, b^2 - 2, c^2 - 2} ≤ f.roots := by
      refine (Multiset.le_iff_subset ?_).mpr ?_
      · simp
        constructor
        constructor
        · by_contra!
          have : (a+b) * (a-b) = 0 := by linarith
          simp at this 
          rcases this with hab | hab
          · simp only [p,hab,zero_add] at hp'
            have hab' : a = -b := by linarith
            simp [r,hp',hab'] at hr
            rw [← pow_two] at hr
            apply sq_eq_one_iff.mp at hr
            rcases hr with hr | hr
            · simp [hp',hab',hr] at h3
            · simp [hp',hr] at h2
          have hab' : a = b := by linarith
          simp [hab'] at h1
        · by_contra!
          have : (a+c) * (a-c) = 0 := by linarith
          simp at this 
          rcases this with hac | hac
          · have hb : b = -1 := by
              simp only [p] at hp'
              linarith only [hp',hac]
            have hac' : a = -c := by linarith
            simp [r,hb,hac'] at hr
            rw [← pow_two] at hr
            apply sq_eq_one_iff.mp at hr
            rcases hr with hr | hr
            · simp [hb,hac',hr] at h1
            · simp [hb,hr] at h2
          have hac' : a = c := by linarith
          simp [hac'] at h3
        · by_contra!
          have : (b+c) * (b-c) = 0 := by linarith
          simp at this 
          rcases this with hbc | hbc
          · simp only [p,hbc,add_assoc,add_zero] at hp'
            have hbc' : b = -c := by linarith
            simp [r,hp',hbc'] at hr
            rw [← pow_two] at hr
            apply sq_eq_one_iff.mp at hr
            rcases hr with hr | hr
            · simp [hp',hbc',hr] at h1
            · simp [hp',hr] at h3
          have hbc' : c = b := by linarith
          simp [hbc'] at h2     
      refine Multiset.subset_iff.mpr ?_
      intro x hx
      simp at hx
      rcases hx with hx |hx |hx
      <;> rw [hx]
      <;> apply hf6
      <;> simp [hf3]
    have : {a^2 - 2, b^2 - 2, c^2 - 2} = f.roots := by
      refine Multiset.eq_of_le_of_card_le hf7 ?_
      rw [hf3] ;simp
    rw [this,hf3]





