import Mathlib 

open Function

/-Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ die voldoen aan
$$
f(x y-1)+f(x) f(y)=2 x y-1
$$
voor alle $x, y \in \mathbb{R}$.-/
theorem algebra_143757 : 
  {f : ℝ → ℝ | ∀ x y, f (x*y - 1) + f x * f y = 2*x*y - 1} = {fun x => -x^2, id} := by 
    ext f 
    simp 
    constructor
    · intro h 
      -- If $f$ is constant, the left side is always the same, while the right side can vary, a contradiction. Therefore, $f$ is not constant. 
      have h1 : ∀ a, f ≠ const _ a := by 
        intro a ha 
        simp [ha] at h 
        linarith [h 0 0, h 1 1]
      -- Now, substitute $x=0$: $f(-1)+f(0) f(y)=-1$, so $f(0) f(y)$ takes the same value for all $y \in \mathbb{R}$. 
      have h2 : ∀ y, f 0 * f y = -1 - f (-1) := by 
        intro y 
        specialize h 0 y 
        simp at h
        linarith 
      -- Since $f$ is not constant, this gives $f(0)=0$. 
      have f0 : f 0 = 0 := by 
        have hh : ∀ x y, f 0 * f x = f 0 * f y := by 
          intro x y; linarith [h2 x, h2 y] 
        simp [forall_or_right] at hh
           
        rcases hh with hl | hr 
        · have hcon : ∀ y, f 0 = f y := hl 0 
          have := h1 (f 0) 
          have : f = const _ (f 0) := by ext y; simp [hcon y]
          tauto
        · exact hr 
      -- We can then immediately conclude that $f(-1)=-1$. 
      have fneg1 : f (-1) = -1 := by simp [f0] at h2; linarith
      -- Now, substitute $x=y=1$: $f(0)+f(1)^{2}=1$, so $f(1)=1$ or $f(1)=-1$.
      have f1 : f 1 = 1 ∨ f 1 = -1 := by 
        specialize h 1 1 
        norm_num [f0, ←pow_two] at h 
        exact h
      -- Substituting $y=1+\frac{1}{x}$ with $x \neq 0$ gives $f(x+1-1)+f(x) f\left(1+\frac{1}{x}\right)=2 x+2-1$, so
      -- $$
      -- f(x) f\left(1+\frac{1}{x}\right)=2 x+1-f(x) \quad \text { for all } x \neq 0
      -- $$
      have h3 : ∀ x, x ≠ 0 → f x * f (1 + 1/x) = 2*x + 1 - f x := by 
        intro x xne0 
        specialize h x (1 + 1/x)
        field_simp at h ⊢
        norm_num [mul_add] at h
        suffices (f x * f ((x + 1) / x)) * x  = (2 * x + 1 - f x) * x by 
          simp [xne0] at this; exact this 
        linarith  
      -- Substituting $y=\frac{1}{x}$ with $x \neq 0$ gives $f(1-1)+f(x) f\left(\frac{1}{x}\right)=2-1$, so
      -- $$
      -- f(x) f\left(\frac{1}{x}\right)=1 \quad \text { for all } x \neq 0
      -- $$
      have h4 : ∀ x, x ≠ 0 → f x * f (1/x) = 1 := by 
        intro x xne0 
        specialize h x (1/x)
        field_simp at h 
        linarith
      -- Substituting $y=1, x=z+1$ gives $f(z+1-1)+f(z+1) f(1)=2 z+2-1$, so
      -- $$
      -- f(z)+f(z+1) f(1)=2 z+1 \quad \text { for all } z
      -- $$
      have h5 : ∀ z, f z + f (z + 1) * f 1 = 2 * z + 1 := by 
        intro z 
        specialize h (z + 1) 1 
        norm_num at h
        linarith
      -- We now choose $z=\frac{1}{x}$ with $x \neq 0$ in this equation and multiply the whole by $f(x)$:
      -- $$
      -- f(x) f\left(\frac{1}{x}\right)+f\left(\frac{1}{x}+1\right) f(1) f(x)=\frac{2}{x} f(x)+f(x) \quad \text { for all } x \neq 0
      -- $$
      have h5' : ∀ x, x ≠ 0 → f x * (f (1 / x) + f (1 / x + 1) * f 1) = f x * (2 * (1 / x) + 1) := by 
        intro x xne0 
        suffices f (1 / x) + f (1 / x + 1) * f 1 = 2 * (1 / x) + 1 from mul_eq_mul_left_iff.2 (Or.inl this)
        exact h5 (1/x)
      -- We rewrite the first and second terms using (2) and (1) respectively, so we get:
      -- $$
      -- 1+2 x f(1)+f(1)-f(x) f(1)=\frac{2}{x} f(x)+f(x) \quad \text { for all } x \neq 0
      -- $$
      -- This can be rewritten as
      -- $$
      -- f(x) \cdot\left(\frac{2}{x}+1+f(1)\right)=1+2 x f(1)+f(1) \quad \text { for all } x \neq 0
      -- $$
      have h5'' : ∀ x, x ≠ 0 → f x * (2/x + 1 + f 1) = 1 + 2 * x * f 1 + f 1 := by 
        intro x xne0 
        specialize h5' x xne0 
        rw [mul_add, ←mul_assoc, add_comm (1/x) 1] at h5'
        rw [h4 x xne0, h3 x xne0] at h5'
        field_simp at h5' ⊢
        linarith
      rcases f1 with f1 | fneg1 
      · -- We had two possible values for $f(1)$. First, let $f(1)=1$. Then we have
      -- $$
      -- f(x)=\frac{2+2 x}{\frac{2}{x}+2}=x \quad \text { if } x \neq 0 \text { and } \frac{2}{x}+2 \neq 0
      -- $$
        right 
        norm_num [f1] at h5''
        have h6 : ∀ x, x ≠ 0 → (2/x + 2 ≠ 0) → f x = x := by 
          intro x xne0 hne0
          replace hne0 : 2/x + 1 + 1 ≠ 0 := by contrapose! hne0; linarith
          have := eq_div_of_mul_eq hne0 (h5'' x xne0 )
          norm_num [this]
          symm
          apply eq_div_of_mul_eq hne0
          field_simp
          linarith
        ext x 
        -- $\frac{2}{x}+2=0$ only if $x=-1$, but we already knew that $f(-1)=-1$. Also, we already had $f(0)=0$. We see that $f(x)=x$ for all $x$
        by_cases hh : x ≠ 0 ∧ 2 / x + 2 ≠ 0
        · exact h6 x hh.1 hh.2
        · simp only [not_and_or] at hh 
          simp at hh
          rcases hh with hh | hh 
          · simp [hh, f0]
          · have : x = -1 := by 
              have : x ≠ 0 := fun x0 => by simp [x0] at hh 
              field_simp at hh 
              linarith  
            simp [this, fneg1]
      · -- On the other hand, let $f(1)=-1$. Then we have
        -- $$
        -- f(x)=\frac{-2 x}{\frac{2}{x}}=-x^{2} \quad \text { if } x \neq 0 \text { and } \frac{2}{x} \neq 0
        -- $$
        left 
        simp [fneg1] at h5''
        ext x 
        -- Since $\frac{2}{x}=0$ cannot occur, we conclude that $f(x)=-x^{2}$ for all $x \neq 0$. Also, $f(0)=0$ satisfies this formula. 
        by_cases xne0 : x ≠ 0 
        · have := h5'' x xne0
          field_simp at this
          linarith
        · simp at xne0 
          simp [xne0, f0]
    · intro h x y
      rcases h with h | h <;> simp_all <;> nlinarith