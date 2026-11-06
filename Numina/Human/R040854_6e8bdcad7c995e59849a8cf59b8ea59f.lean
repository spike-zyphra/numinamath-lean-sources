import Mathlib

/-Let $f$ be a function taking the integers to the integers such that
\[f(m + n) + f(mn - 1) = f(m) f(n) + 2\]for all integers $m$ and $n.$

Let $n$ be the number of possible values of $f(2),$ and let $s$ be the sum of all possible values of $f(2).$  Find $n \times s.$-/
theorem algebra_13575 {f : ℤ → ℤ} (h : ∀ m n, f (m + n) + f (m * n - 1) = f m * f n + 2) :
    ∃(S : Finset ℤ), S = {y | y = f 2} ∧ S.card * (∑ y ∈ S, y) = 5 := by
  have : {y | y = f 2} = {5} := by
    ext n
    simp

    -- Setting $n = 0,$ in h, we get f(m) + f(-1) = f(m) f(0) + 2.
    have eq₁ : ∀ m, f m + f (-1) = f m * f 0 + 2 := by
      intro m
      specialize h m 0
      simp at h
      exact h

    -- If $f(0) \neq 1,$ then $f(m)$ is equal to some constant, say $c.$
    by_cases f0 : f 0 ≠ 1
    . -- because for all integer m, f m = (2 - f (-1))/(1 - f 0)
      -- and, (2 - f (-1))/(1 - f 0) is a constant, say c.
      have eq₂: ∀m, (f m)  = (2 - f (-1))/(1 - f 0) := by
        intro m
        specialize eq₁ m
        apply Int.eq_ediv_of_mul_eq_right (sub_ne_zero_of_ne (Ne.symm f0))
        linarith
      obtain ⟨c, hc⟩ := (by simp: ∃c, c = (2 - f (-1))/(1 - f 0))
      specialize eq₁ 0
      have : f 0 = c := by
        specialize eq₂ 0
        rw [hc.symm] at eq₂
        exact eq₂
      rw [this] at eq₁
      have : f (-1) = c := by
        specialize eq₂ (-1)
        rw [hc.symm] at eq₂
        exact eq₂
      rw [this] at eq₁
      -- Then, 2c = c^2 + 2, which has no integer solutions.
      have : (c - 1)^2 = -1 := by linarith
      linarith [sq_nonneg (c - 1)]

    -- Therefore, $f(0) = 1,$ and then $f(-1) = 2.$
    simp at f0

    -- Setting $n = 1,$ in h, we get
    have eq₂: ∀m, f (m + 1) + f (m - 1) = f 1 * f m + 2 := by
      intro m
      specialize h m 1
      simp at h
      linarith

    -- Let $a = f(1)$; then f(m + 1) = af(m) - f(m - 1) + 2.
    obtain ⟨a, f1⟩ := (by simp: ∃a, f 1 = a)
    rw [f1] at eq₂
    -- Since $f(0) = 1$ and $f(1) = a,$
    -- f(2) = af(1) - f(0) + 2 = a^2 + 1
    have f2 : f 2 = a^2 + 1 := by
      specialize eq₂ 1
      simp at eq₂
      rw [f1, f0] at eq₂
      linarith
    -- f(3) = af(2) - f(1) + 2 = a^3 + 2,
    have f3 : f 3 = a^3 + 2 := by
      specialize eq₂ 2
      simp at eq₂
      rw [f1, f2] at eq₂
      linarith
    -- f(4) = af(3) - f(2) + 2 = a^4 - a^2 + 2a + 1,
    have f4 : f 4 = a^4 - a^2 + 2*a + 1 := by
      specialize eq₂ 3
      simp at eq₂
      rw [f2, f3] at eq₂
      linarith
    -- f(5) = af(4) - f(3) + 2 = a^5 - 2a^3 + 2a^2 + a.
    have f5 : f 5 = a^5 - 2*a^3 + 2*a^2 + a := by
      specialize eq₂ 4
      simp at eq₂
      rw [f4, f3] at eq₂
      linarith
    have ra: a = 0 ∨ a = 1 ∨ a = 2 := by


      -- Setting $m = n = 2,$ in h, we get f(4) + f(3) = f(2)^2 + 2.
      have f4₂ : f 4 + f 3 = f 2^2 + 2 := by
        specialize h 2 2
        simp at h
        linarith

      -- Then $(a^4 - a^2 + 2a + 1) + (a^3 + 2) = (a^2 + 1)^2 + 2,$, which simplifies to
      -- a^3 - 3a^2 + 2a = 0.
      have : a^3 - 3*a^2 + 2*a = 0 := by
        rw [f4, f3, f2] at f4₂
        linarith

      -- This factors as $a(a - 1)(a - 2) = 0.$ Hence, $a \in \{0, 1, 2\}.$
      have : a * (a - 1) * (a - 2) = 0 := by linarith
      simp at this
      omega

    -- Setting $m = 2$ and $n = 3,$ we get, f(5) + f(5) = f(2) f(3) + 2.
    have f5₂ : f 5 + f 5 = f 2 * f 3 + 2 := by
      specialize h 2 3
      simp at h
      linarith
    -- Then $2(a^5 - 2a^3 + 2a^2 + a) = (a^2 + 1)(a^3 + 2) + 2.$
    rw [f5, f3, f2] at f5₂
    -- Checking $a = 0,$ $a = 1,$ and $a = 2,$ we find that the only value that works is $a = 2.$
    obtain (r₀ | r₁ | ra) := ra
    . -- check a = 0
      rw [r₀] at f5₂
      linarith
    . -- check a = 1
      rw [r₁] at f5₂
      linarith
    rw [ra] at eq₂ f1 f2 f3 f4 f5
    -- f 2 = 5
    -- f 3 = 10
    -- f 4 = 17
    -- f 5 = 26
    simp at f2 f3 f4 f5
    -- By a straight-forward induction argument, we can show that f(n) = n^2 + 1 for all integers n.
    -- We can check that this function works.
    -- Therefore, $n = 1$ and $s = 5,$ so $n \times s = \boxed{5}.
    rw [f2]
  rw [this]
  simp
