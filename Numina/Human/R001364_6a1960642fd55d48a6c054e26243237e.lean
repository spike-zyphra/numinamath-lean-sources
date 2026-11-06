import Mathlib

/-Find all functions $f:(0, \infty) \rightarrow(0, \infty)$ such that
  $$ \frac{f(p)^{2}+f(q)^{2}}{f\left(r^{2}\right)+f\left(s^{2}\right)}=\frac{p^{2}+q^{2}}{r^{2}+s^{2}} $$  for all $p, q, r, s>0$ with $p q=r s$.-/
theorem algebra_23716 : {f : ℝ → ℝ | (∀ x > 0 , f x > 0) ∧
  (∀ p q r s, p > 0 ∧ q > 0 ∧ r > 0 ∧ s > 0 ∧ p * q = r * s →
  (f p ^ 2 + f q ^ 2) / (f (r ^ 2) + f (s ^ 2)) = (p ^ 2 + q ^ 2) / (r ^ 2 + s ^ 2))} =
  {f : ℝ → ℝ | (∀ x > 0 , f x = 1 / x) ∨ ∀ x > 0 , f x = x} := by
  ext f
  constructor
  · rintro ⟨f_def,f_eq⟩
    simp
    -- Let $f$ satisfy the given condition.
    -- Setting $p=q=r=s=1$ yields $f(1)^{2}=f(1)$ and hence $f(1)=1$.
    have hf1 : f 1 = 1 := by
      specialize f_eq 1 1 1 1
      simp [← two_mul,mul_div_mul_left,pow_two] at f_eq
      exact f_eq
    -- Now take any $x\gt0$ and set $p=x, q=1, r=s=\\sqrt{x}$ to obtain $$ \\frac{f(x)^{2}+1}{2 f(x)}=\\frac{x^{2}+1}{2 x} . $$
    have fx_eq : ∀ x > 0 , ((f x)^2 + 1) / (2 * f x) = (x^2 + 1) / (2 * x) := by
      intro x x_pos
      specialize f_eq x 1 (√ x) (√ x)
      simp [x_pos,hf1,← two_mul,← pow_two] at f_eq
      have : (√ x) ^ 2 = x := by refine Real.sq_sqrt (by linarith)
      simp [this] at f_eq
      exact f_eq
    -- This recasts into $$ \\begin{gathered} x f(x)^{2}+x=x^{2} f(x)+f(x), \\ (x f(x)-1)(f(x)-x)=0 . \\end{gathered} $$
    have fx_eq' : ∀ x > 0 , (x * f x - 1) * (f x - x) = 0 := by
      intro x x_pos
      specialize fx_eq x x_pos
      have h1 : 2 * f x ≠ 0 := by simp ;specialize f_def x x_pos ;linarith
      have h2 : 2 * x ≠ 0 := by linarith
      apply (div_eq_div_iff h1 h2).mp at fx_eq
      have : (f x ^ 2 + 1) * (2 * x) - (x ^ 2 + 1) * (2 * f x) = 2 * (x * f x - 1) * (f x - x) := by ring
      have : 2 * (x * f x - 1) * (f x - x) = 0 := by rw [← this] ;exact sub_eq_zero_of_eq fx_eq
      rw [mul_assoc] at this
      rcases mul_eq_zero.mp this with h | h
      · linarith
      exact h
    -- And thus, $$ \\text { for every } x\gt0, \\text { either } f(x)=x \\text { or } f(x)=\\frac{1}{x} \\text {. } $$
    simp at fx_eq'
    -- Obviously, if $$ f(x)=x \\quad \\text { for all } x\gt0 \\quad \\text { or } \\quad f(x)=\\frac{1}{x} \\quad \\text { for all } x\gt0 $$
    -- then the condition of the problem is satisfied.
    -- We show that actually these two functions are the only solutions.
    -- So let us assume that there exists a function $f$ satisfying the requirement, other than those in (2).
    by_contra! h
    -- Then $f(a) \\neq a$ and $f(b) \\neq 1 / b$ for some $a, b\gt0$.
    rcases h with ⟨⟨b,hb,hb'⟩,⟨a,ha,ha'⟩⟩
    -- By (1), these values must be $f(a)=1 / a, f(b)=b$.
    have hb'' : f b = b := by
      specialize fx_eq' b hb
      rcases fx_eq' with h | h
      · have : f b = 1 / b := by
          refine eq_one_div_of_mul_eq_one_right ?_
          apply sub_eq_iff_eq_add.mp at h
          rw [h,zero_add]
        exact False.elim (hb' (by simp [this]))
      apply sub_eq_iff_eq_add.mp at h
      rw [h,zero_add]
    have ha'' : f a = 1 / a := by
      specialize fx_eq' a ha
      rcases fx_eq' with h | h
      · apply sub_eq_iff_eq_add.mp at h
        rw [zero_add] at h
        apply eq_one_div_of_mul_eq_one_right at h
        exact h
      apply sub_eq_iff_eq_add.mp at h
      rw [zero_add] at h
      exact False.elim (ha' h)
    -- Applying now the equation with $p=a, q=b, r=s=\\sqrt{a b}$ we obtain $\\left(a^{-2}+b^{2}\\right) / 2 f(a b)=\\left(a^{2}+b^{2}\\right) / 2 a b ;$
    have ab_eq : ((1/a)^2 + b ^ 2) / (2 * f (a * b)) = (a ^ 2 + b ^ 2) / (2 * a * b) := by
      specialize f_eq a b (√ (a * b)) (√ (a * b))
      simp [ha,hb,← two_mul,← pow_two] at f_eq
      have : (√ (a * b)) ^ 2 = a * b := by refine Real.sq_sqrt (Left.mul_nonneg (by linarith) (by linarith))
      simp [this] at f_eq
      rw [mul_assoc,← f_eq,ha'',hb'']
    -- equivalently, $$ f(a b)=\\frac{a b\\left(a^{-2}+b^{2}\\right)}{a^{2}+b^{2}} . $$
    -- We know however (see (1)) that $f(a b)$ must be either $a b$ or $1 / a b$.
    rcases fx_eq' (a*b) (mul_pos ha hb) with h | h
    -- if $f(a b)=1 / a b$ then (3) gives $a^{2} b^{2}\\left(a^{-2}+b^{2}\\right)=a^{2}+b^{2}$, whence $b=1$, in contradiction to $f(b) \\neq 1 / b$.
    · have fab : f (a * b) = 1 / (a * b) := by
        apply sub_eq_iff_eq_add.mp at h
        rw [zero_add] at h
        apply eq_one_div_of_mul_eq_one_right at h
        exact h
      rw [fab] at ab_eq
      ring_nf at ab_eq
      simp [pow_two,← add_mul] at ab_eq
      rw [add_mul,mul_assoc,inv_mul_cancel₀ (by linarith),add_mul a,mul_assoc a⁻¹,mul_assoc b b b⁻¹,mul_inv_cancel₀ (by linarith)] at ab_eq
      simp [add_mul,add_comm,mul_comm a,mul_comm (b*b*a),← mul_assoc] at ab_eq
      rcases ab_eq with h|h
      have : (b ^ 2) ^ 2 = 1 := by rw [pow_two,pow_two,← mul_assoc,h,inv_mul_cancel₀ (by linarith)]
      simp at this
      rcases this with ⟨h'|h'⟩ | h'
      · simp [h'] at hb'; exact False.elim (hb' hf1)
      · linarith
      · have : b ^ 2 > 0 := by exact sq_pos_of_pos hb
        linarith
      linarith
    -- If $f(a b)=a b$ then by (3) $a^{-2}+b^{2}=a^{2}+b^{2}$, so that $a=1$.
    -- But, as $f(1)=1$, this contradicts the relation $f(a) \\neq a$.
    have fab : f (a * b) = a * b := by
      apply sub_eq_iff_eq_add.mp at h
      rw [zero_add] at h
      exact h
    rw [fab] at ab_eq
    ring_nf at ab_eq
    simp [pow_two,← add_mul] at ab_eq
    rcases ab_eq with h|h
    · have h' : a * (a⁻¹ * (b * b) + (a ^ 3)⁻¹) = a * (a + a⁻¹ * (b * b)) := by rw [h]
      rw [mul_add,← mul_assoc,mul_inv_cancel₀ (by linarith),one_mul] at h'
      rw [mul_add,← mul_assoc,mul_inv_cancel₀ (by linarith),one_mul,add_comm] at h'
      simp at h'
      rcases h' with h''|h''
      · have : (a ^ 2) ^ 2 = 1 := by
          rw [pow_two,pow_two,mul_assoc,← pow_three]
          nth_rewrite 1 [← h'']
          rw [inv_mul_cancel₀ (by simp ;linarith)]
        simp at this
        rcases this with ⟨h'|h'⟩ | h'
        · simp [h'] at ha'; exact False.elim (ha' hf1)
        · linarith
        · have : a ^ 2 > 0 := by exact sq_pos_of_pos ha
          linarith
      · linarith
    · linarith
  · rintro (h | h)
    · simp
      constructor
      · intro x x_pos
        simp [h x x_pos, x_pos]
      · intro p q r s hp hq hr hs hpqrs
        simp [h p hp, h q hq, h (r ^ 2) (by positivity), h (s ^ 2) (by positivity)]
        field_simp
        rw [← mul_pow, ← hpqrs]
        ring_nf
    · simp
      constructor
      · intro x x_pos
        simp [h x x_pos, x_pos]
      · intro p q r s hp hq hr hs hpqrs
        simp [h p hp, h q hq, h (r ^ 2) (by positivity), h (s ^ 2) (by positivity)]

