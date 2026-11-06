import Mathlib

/- Determine all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ that satisfy

$$
f(f(x)+y)+x f(y)=f(x y+y)+f(x)
$$

for all real numbers $x$ and $y$. -/
theorem algebra_604850 :
  {f : ℝ → ℝ | ∀ x y, f (f x + y) + x * f y = f (x * y + y) + f x} = {id, 0} := by
  ext f
  simp
  constructor
  -- We verify that f(x) = x and f(x) = 0 are solutions
  swap
  {
    rintro (rfl | rfl)
    all_goals
      intro x y
      simp
    ring
  }
  -- Let f satisfy the functional equation P
  rintro P
  -- Claim 1: f(0) = 0
  -- We prove this by considering P(0,y) and P(x,0)
  -- Let a = -f(0). If f(a) = 0, then af(0) = 0, which means f(0) = 0
  have H₁ : f 0 = 0 := by
    --
    have h₁ y := P 0 y
    have h₂ x := P x 0
    simp at h₁ h₂
    specialize h₁ (-f 0)
    simp at h₁
    let a := -f 0
    change f a = 0 at h₁
    specialize h₂ a
    simp [h₁] at h₂
    rcases h₂ with h₂ | h₂
    . simp [a] at h₂
      exact h₂
    . exact h₂
  -- Using P(x,0) and f(0) = 0, we get f(f(x)) = f(x)
  have K₁ x : f (f x) = f x := by
    specialize P x 0
    simp [H₁] at P
    exact P
  -- Claim 2: Either f(1) = 1 or f is identically zero
  -- We prove this by considering P(f(x),1) and using f(f(x)) = f(x)
  have H₂ : f 1 = 1 ∨ ∀ x, f x = 0 := by
    have h₂ x : f x * f 1 = f x := by
      specialize P (f x) 1
      simp [K₁] at P
      exact P
    by_cases h₃ : f 1 = 1
    . exact Or.inl h₃
    . refine Or.inr (fun x => ?_)
      specialize h₂ x
      contrapose! h₃
      simp [h₃] at h₂
      exact h₂
  -- Without loss of generality, assume f(1) = 1
  wlog K₂ : f 1 = 1
  {
    simp [K₂] at H₂
    exact Or.inr (funext H₂)
  }
  -- Claim 3: If f(a) = 0, then a = 0
  -- This is proved using P(a,1) and P(1,a)
  have H₃ {a} (ha : f a = 0) : a = 0 := by
    have h₁ := P a 1
    have h₂ := P 1 a
    simp [ha, K₂] at h₁ h₂
    ring_nf at h₁ h₂
    have h₃ : f (a * 2) = a := by linear_combination -h₁ - h₂
    have h₄ := h₃
    apply_fun f at h₄
    rw [K₁, ha] at h₄
    rw [h₃] at h₄
    exact h₄
  -- Final step: Consider P(x, x-f(x))
  -- This leads to f(-1) = -1, and then
  -- Using P(-1,y+1) we get f(y+1) = f(y) + 1
  -- Finally, P(x,1) shows that f(x) = x
  have h₁ x := P x (x - f x)
  replace h₁ x : x * f (x - f x) = f ((x - f x) * (x + 1)) := by
    specialize h₁ x
    ring_nf at h₁ ⊢
    linear_combination h₁
  specialize h₁ (-1)
  simp [H₁] at h₁
  apply H₃ at h₁
  replace h₁ : f (-1) = -1 := by linear_combination -h₁
  have h₂ y := P (-1) (y + 1)
  simp [h₁] at h₂
  ring_nf at h₂
  simp [H₁] at h₂
  replace h₂ y : f (y + 1) = f y + 1 := by
    specialize h₂ y
    ring_nf
    linear_combination -h₂
  have h₃ x := P x 1
  simp [h₂, K₁, K₂] at h₃
  exact Or.inl (funext (fun x ↦ (h₃ x).symm))
