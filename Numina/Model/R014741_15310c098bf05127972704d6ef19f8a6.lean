import Mathlib

theorem algebra_10250 : {n : ℤ | (n + 3) * (n - 7) ≤ 0}.encard = 11 := by
  have h1 : {n : ℤ | (n + 3) * (n - 7) ≤ 0} = Set.Icc (-3 : ℤ) 7 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Forward direction: if $(n + 3) * (n - 7) ≤ 0$, then $-3 ≤ n ≤ 7$.
      intro h
      constructor
      · -- Show that $-3 ≤ n$.
        nlinarith
      · -- Show that $n ≤ 7$.
        nlinarith
    · -- Backward direction: if $-3 ≤ n ≤ 7$, then $(n + 3) * (n - 7) ≤ 0$.
      rintro ⟨h1, h2⟩
      nlinarith
  rw [h1]
  rw [Set.encard]
  simp
  <;> try { native_decide }