import Mathlib

/- $7 \cdot 1$ Prove that there do not exist integers $a, b, c, d$ satisfying the following equations

$$

\left\{\begin{array}{l}
a b c d-a=1961, \\
a b c d-b=961, \\
a b c d-c=61, \\
a b c d-d=1 .
\end{array}\right.

$$

(24th Moscow Mathematical Olympiad, 1961) -/
theorem number_theory_164004 :
    ¬∃ (a b c d : ℤ), a * b * c * d - a = 1961 ∧ a * b * c * d - b = 961 ∧ a * b * c * d - c = 61 ∧ a * b * c * d - d = 1 := by 
  -- Assume that there exist a, b, c, d satisfying the equations.
  -- Derive a contradiction.
  intro ⟨a, b, c, d, h1, h2, h3, h4⟩
  -- Show that a is odd.
  have ha : Odd a := by
    -- 1961 is odd, so a * b * c * d - a = a * (b * c * d - 1) is odd.
    apply_fun Odd at h1
    rw [show a * b * c * d - a = a * (b * c * d - 1) by ring] at h1
    -- a * x is odd implies that a is odd.
    simp [Int.odd_mul, show Odd (1961 : ℤ) by decide] at h1
    exact h1.1
  -- Show that b is odd.
  have hb : Odd b := by
    apply_fun Odd at h2
    rw [show a * b * c * d - b = b * (a * c * d - 1) by ring] at h2
    simp [Int.odd_mul, show Odd (961 : ℤ) by decide] at h2
    exact h2.1
  -- Show that c is odd.
  have hc : Odd c := by
    apply_fun Odd at h3
    rw [show a * b * c * d - c = c * (a * b * d - 1) by ring] at h3
    simp [Int.odd_mul, show Odd (61 : ℤ) by decide] at h3
    exact h3.1
  -- Show that d is odd.
  have hd : Odd d := by
    apply_fun Odd at h4
    rw [show a * b * c * d - d = d * (a * b * c - 1) by ring] at h4
    simp [Int.odd_mul, show Odd (1 : ℤ) by decide] at h4
    exact h4.1
  -- We get that a * b * c * d is odd.
  have h : Odd (a * b * c * d) := by simp_all [Int.odd_mul]
  -- We get that a * b * c * d - a is even (as the difference
  -- of odd numbers), a contradiction.
  apply_fun Odd at h4
  simp [Int.odd_sub, h] at h4
  contrapose! h4
  simp [hd]