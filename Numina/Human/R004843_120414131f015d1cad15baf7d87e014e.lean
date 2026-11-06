import Mathlib

/- Do there exist? functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that
a) $f$ is a surjective function; and
b) $f(f(x))=(x-1) f(x)+2$ for all $x$ real. -/
theorem algebra_604176 :
  ¬∃ f : ℝ → ℝ, f.Surjective ∧ ∀ x : ℝ, f (f x) = (x - 1) * f x + 2 := by
  rintro ⟨f, hsurj, hf⟩
  -- We write f(f(f(x))) in two ways.
  -- And we get the following equation H:
  have H (x : ℝ) : f ((x - 1) * f x + 2) = f x * ((f x - 1) * (x - 1) + 2) := by
    calc f ((x - 1) * f x + 2)
      _ = f (f (f x)) := by rw [hf x]
      _ = (f x - 1) * f (f x) + 2 := by rw [hf (f x)]
      _ = (f x - 1) * ((x - 1) * f x + 2) + 2 := by rw [hf x]
      _ = f x * ((f x - 1) * (x - 1) + 2) := by ring
  -- Let f(a) = 0.
  obtain ⟨a, ha⟩ := hsurj 0
  -- We have f(0) = 2.
  have h₁ : f 0 = 2 := by
    -- Plug in a = 0 into the original equation.
    specialize hf a
    simp [ha] at hf
    exact hf
  -- We have f(2) = 0.
  have h₂ : f 2 = 0 := by
    -- Plug in a = 0 into the original equation.
    specialize hf 0
    simp [h₁] at hf
    exact hf
  -- We have f(1) = 0.
  have h₃ : f 1 = 0 := by
    -- Plug in a = 1 into H.
    specialize H 1
    simp [h₂] at H
    exact H
  -- Let f(b) = 1.
  obtain ⟨b, hb⟩ := hsurj 1
  -- We have b = -1.
  obtain rfl : b = -1 := by
    -- Plug in b = -1 into H.
    specialize hf b
    simp [hb, h₃] at hf
    linarith only [hf]
  -- Let f(c) = -1.
  obtain ⟨c, hc⟩ := hsurj (-1)
  -- We have c = 2.
  obtain rfl : c = 2 := by
    -- Plug in c = 2 into H.
    specialize hf c
    simp [hc, hb] at hf
    linarith only [hf]
  -- Now 0 = f(2) = -1, contradiction.
  linarith only [h₂, hc]
