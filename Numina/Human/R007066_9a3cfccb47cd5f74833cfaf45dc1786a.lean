import Mathlib

/- Let $S$ be the set of positive real numbers. Find all functions $f: S^{3} \rightarrow S$ such that, for all positive real numbers $x, y, z$ and $k$, the following three conditions are satisfied:
(i) $x f(x, y, z)=z f(z, y, x)$;
(ii) $f\left(x, k y, k^{2} z\right)=k f(x, y, z)$;
(iii) $f(1, k, k+1)=k+1$.
(United Kingdom) -/
theorem algebra_604314 (f : ℝ → ℝ → ℝ → ℝ)
    (h₀ : ∀ x y z, 0 < x → 0 < y → 0 < z → x * f x y z = z * f z y x)
    (h₁ : ∀ x y z k, 0 < x → 0 < y → 0 < z → 0 < k → f x (k * y) (k ^ 2 * z) = k * f x y z)
    (h₂ : ∀ k, 0 < k → f 1 k (k + 1) = k + 1) :
    ∀ x y z, 0 < x → 0 < y → 0 < z → f x y z = (y + Real.sqrt (y ^ 2 + 4 * x * z)) / (2 * x) := by
    -- It follows from the properties of function $f$ that, for all $x, y, z, a, b&gt;0$,
    -- $f\left(a^{2} x, a b y, b^{2} z\right)=b f\left(a^{2} x, a y, z\right)=b \cdot \frac{z}{a^{2} x} f\left(z, a y, a^{2} x\right)=\frac{b z}{a x} f(z, y, x)=\frac{b}{a} f(x, y, z)$.
    have h₃ : ∀ x y z a b, 0 < x → 0 < y → 0 < z → 0 < a → 0 < b → f (a ^ 2 * x) (a * b * y) (b ^ 2 * z) = b / a * f x y z := by
      intro x y z a b hx hy hz ha hb
      have h1 := h₁ (a ^ 2 * x) (a * y) z b (by apply mul_pos; exact sq_pos_of_pos ha ;exact hx) (mul_pos ha hy) hz hb
      have h2 := h₀ (a ^ 2 * x) (a * y) z (by apply mul_pos; exact sq_pos_of_pos ha ;exact hx) (mul_pos ha hy) hz
      have h3 := h₁ z y x a hz hy hx ha
      have h4 := h₀ z y x hz hy hx
      rw [mul_comm a b,mul_assoc,h1]
      rw [mul_comm] at h2 ;apply (eq_div_iff (by refine Ne.symm (ne_of_lt (by apply mul_pos; exact sq_pos_of_pos ha ;exact hx)))).mpr at h2
      rw [h2,h3]
      rw [mul_comm] at h4 ;apply (eq_div_iff (Ne.symm (ne_of_lt hz))).mpr at h4
      rw [h4,pow_two] ;field_simp ;ring
    -- We shall choose $a$ and $b$ in such a way that the triple $\left(a^{2} x, a b y, b^{2} z\right)$ is of the form $(1, k, k+1)$ for some $k$ :
    -- namely, we take $a=\frac{1}{\sqrt{x}}$ and $b$ satisfying $b^{2} z-a b y=1$, which upon solving the quadratic equation yields
    -- $b=\frac{y+\sqrt{y^{2}+4 x z}}{2 z \sqrt{x}}$ and $k=\frac{y\left(y+\sqrt{y^{2}+4 x z}\right)}{2 x z}$.
    intro x y z hx hy hz
    have : ∃ a , a = 1 / √ x ∧ a > 0:= by
      refine exists_eq_left.mpr ?_
      refine one_div_pos.mpr ?_ ;exact Real.sqrt_pos_of_pos hx
    rcases this with ⟨a, ⟨ha1,ha2⟩⟩
    have : ∃ b , b ^ 2 * z - a * b * y = 1 ∧ b > 0 ∧
      b = (y + Real.sqrt (y ^ 2 + 4 * x * z)) / (2 * z * Real.sqrt x) := by
      use (y + Real.sqrt (y ^ 2 + 4 * x * z)) / (2 * z * Real.sqrt x)
      constructor
      rw [ha1] ;field_simp ;ring_nf
      have : 4 = 2 * 2 := rfl
      rw [this,pow_mul,Real.sq_sqrt,Real.sq_sqrt] ;ring
      apply add_nonneg ;exact sq_nonneg y ;simp ;apply mul_nonneg ;linarith ;linarith ;linarith
      constructor
      apply div_pos ;apply add_pos ;exact hy
      refine Real.sqrt_pos_of_pos ?_ ;apply add_pos ;exact sq_pos_of_pos hy
      refine mul_pos (mul_pos (by simp) hx) hz
      refine mul_pos (mul_pos (by simp) hz) (Real.sqrt_pos_of_pos hx) ;rfl
    rcases this with ⟨b, ⟨hb1,hb2,hb3⟩⟩
    -- Now we easily obtain
    -- $$ f(x, y, z)=\frac{a}{b} f\left(a^{2} x, a b y, b^{2} z\right)=\frac{a}{b} f(1, k, k+1)=\frac{a}{b}(k+1)=\frac{y+\sqrt{y^{2}+4 x z}}{2 x} . $$
    -- It is directly verified that $f$ satisfies the problem conditions.
    specialize h₃ x y z a b hx hy hz ha2 hb2
    specialize h₂ (a * b * y) (by apply mul_pos ?_ hy;apply mul_pos ha2 hb2)
    have : a ^ 2 * x = 1 := by simp [ha1] ;field_simp
    have this' : b ^ 2 * z = a * b * y + 1 := by rw [← hb1] ;field_simp
    rw [this,this',h₂,mul_comm (b/a)] at h₃
    apply (div_eq_iff (by refine div_ne_zero_iff.mpr (by constructor ;linarith ;linarith))).mpr at h₃
    rw [← h₃,ha1,hb3] ;field_simp ;ring_nf ;rw [Real.sq_sqrt] ;ring_nf
    have : √x ^ 3 = √x * x := by rw [pow_three] ;field_simp
    rw [this] ;ring
    apply add_nonneg ;exact sq_nonneg y ;apply mul_nonneg ?_ (by simp) ;apply mul_nonneg ;linarith ;linarith
    