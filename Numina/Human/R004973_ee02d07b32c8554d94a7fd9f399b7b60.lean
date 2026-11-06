import Mathlib 


/-Consider the functions $f$ defined on the set of integers such that

$$
f(x)=f\left(x^{2}+x+1\right),
$$

for all integers $x$. Find

(a) all even functions,

(b) all odd functions of this kind.-/
theorem algebra_604864_a : {f : ℤ → ℝ | (∀ x, f x = f (x^2 + x + 1)) ∧ Function.Even f} = 
  {f | ∃ a, ∀ x, f x = a} := by 
    ext f 
    simp 
    constructor <;> intro h
    · -- For \( f \) even, we have \( f(x-1) = f\left((x-1)^{2} + (x-1) + 1\right) = f\left(x^{2} - x + 1\right) = f\left((-x)^{2} - x + 1\right) = f(-x) = f(x) \) for any \( x \in \mathbb{Z} \).
      have h1 : ∀ x, f (x - 1) = f x := by 
        intro x
        have h1 := h.1 (x - 1)
        rw [show (x - 1) ^ 2 + (x - 1) + 1 = x^2 - x + 1 by linarith] at h1
        have h2 := h.1 (-x)
        rw [h.2 x] at h2
        simp [h1, h2]
        congr
      --  Hence \( f \) has a constant value; any constant will do.
      use f 0 
      intro x 
      wlog xnonneg : 0 ≤ x
      · have h2 : 0 ≤ (-x) := by linarith
        rw [←h.2 x]
        exact this f h h1 (-x) h2
      · rw [←Int.toNat_of_nonneg xnonneg]
        induction' x.toNat with x hind 
        · simp 
        · have := h1 (x + 1)
          simp at this
          push_cast
          linarith 
    · -- Verify that the constant function satisfy the conditon.
      obtain ⟨a, h1⟩ := h 
      exact ⟨by intro x; simp [h1 x, h1 (x^2 + x + 1)], by intro x; simp [h1 x, h1 (-x)]⟩ 
      

theorem algebra_604864_b : {f : ℤ → ℝ | (∀ x, f x = f (x^2 + x + 1)) ∧ Function.Odd f} = 
  {f | f = 0} := by 
    ext f 
    simp 
    constructor <;> intro h
    · --  For \( f \) odd, a similar computation yields \( f(x-1) = -f(x) \). 
      have h1 : ∀ x, f (x - 1) = - f x := by 
        intro x
        have h1 := h.1 (x - 1)
        rw [show (x - 1) ^ 2 + (x - 1) + 1 = x^2 - x + 1 by linarith] at h1
        have h2 := h.1 (-x)
        rw [h.2 x, show (-x) ^ 2 + -x + 1 = x ^ 2 - x + 1 by linarith, ← h1] at h2
        exact h2.symm
      -- Since \( f(0) = 0 \), we see that \( f(x) = 0 \) for all \( x \in \mathbb{Z} \).
      have h2 : ∀ x, f x = 0 := by 
        intro x 
        wlog xnonneg : 0 ≤ x
        · have h2 : 0 ≤ (-x) := by linarith
          suffices f (-x) = 0 by rw [h.2 x] at this; linarith
          exact this f h h1 (-x) h2
        · rw [←Int.toNat_of_nonneg xnonneg]
          induction' x.toNat with x hind 
          · simp [Function.Odd.map_zero h.2]
          · have := h1 (x + 1)
            simp at this
            push_cast
            linarith 
      ext x 
      simp [h2 x]
    · -- Verify that zero function satisfy the conditon.
      simp [h, Function.Odd]
      