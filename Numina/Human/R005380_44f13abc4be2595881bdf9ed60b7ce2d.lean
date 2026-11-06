import Mathlib

/- Determine all real numbers $A, B$ and $C$ such that there exists a real function $f$ that satisfies

$$
f(x+f(y))=A x+B y+C
$$

for all real $x$ and $y$. -/
theorem algebra_607712: {(a, b, c): ℝ × ℝ × ℝ | ∃ f: ℝ → ℝ, ∀ x y: ℝ, f (x + f y) = a * x + b * y + c} = { (a, b, _c) | b = a ^ 2 ∧ a ≠ -1 } ∪ {(-1, 1, 0)} := by
  apply Set.ext
  intro ⟨a, b, c⟩
  simp
  constructor
  . intro ⟨f, hf⟩
    -- set $x = x - f(0)$ in the equation, we find that $f(x) = a x + c - a f(0)$
    have hf_leaner : ∀ x: ℝ, f x = a * x + c - a * f 0 := by
      intro z
      have h1 := hf (z - f 0) 0
      simp at h1
      linear_combination h1
    -- using the equation $f(x) = a x + c - a f(0)$, we can rewrite the original equation as $f(x + a y + c - a f(0)) = a x + b y + c$
    -- we get $\forall y, (a ^2 - b) * y - a * (a + 1) * f 0 + a * c = 0$
    conv at hf =>
      intro x y
      rw [hf_leaner, hf_leaner, <-sub_eq_zero]
      rw [show a * (x + (a * y + c - a * f 0)) + c - a * f 0 - (a * x + b * y + c) = (a ^ 2 - b) * y - a * (a + 1) * f 0 + a * c by ring ]
    specialize hf 0
    -- having $\forall y, (a ^ 2 - b) * y - a * (a + 1) * f 0 + a * c = 0$, we can conclude that $a ^ 2 - b = 0$ and $- a * (a + 1) * f 0 + a * c = 0$
    have b_eq_a_sq : b = a ^ 2 := by linear_combination (hf 0) - (hf 1)
    have h' : - a * (a + 1) * f 0 + a * c = 0 := by linear_combination (hf 0)
    by_cases h : a = -1
    . left
      -- if $a = -1$, we have $c = 0$ from $- a * (a + 1) * f 0 + a * c = 0$
      simp [h, b_eq_a_sq]
      rw [h] at h'
      simp at h'
      exact h'
    . right
      exact And.intro b_eq_a_sq h
  . intro h
    cases h with
    | inl h =>
      -- the case that $a=-1, b=1, c=0$
      rw [h.1, h.2.1, h.2.2]
      -- we can easily find a function $f(x) = -x$ that satisfies the equation
      use (λ x => -x)
      simp
      intro x y
      rw [add_comm]
    | inr h =>
      -- the case that $b = a ^ 2$ and $a ≠ -1$
      rw [h.1]
      -- we have $f(x) = ax + c - af(0)$
      -- setting $x = 0$ in it, we get $f(0) = c / (1 + a)$
      -- so $f(x) = a x + c - a c / (1 + a)$
      use (λ x => a * x + c - a * c / (1 + a))
      simp
      intro x y
      calc a * (x + (a * y + c - a * c / (1 + a))) + c - a * c / (1 + a) = a * x + a * a * y + a * c + c - a * c * (1 + a) / (1 + a) := by ring
        _ = a * x + a * a * y + a * c + c - a * c := by rw [mul_div_cancel_right₀]; rw [ne_eq, add_eq_zero_iff_eq_neg']; exact h.2
        _ = a * x + a ^ 2 * y + c := by ring
