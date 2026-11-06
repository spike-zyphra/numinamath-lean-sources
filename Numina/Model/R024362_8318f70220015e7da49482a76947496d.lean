import Mathlib

def f (A B : Set ℕ) := {x | ∃ m ∈ A, ∃ n ∈ B, x = m + n}

theorem algebra_326586 {A B : Set ℕ} (hA : A = {1, 2, 3}) (hB : B = {1, 2}) :
    ∑ᶠ x ∈ f A B, x = 14 := by
  rw [show f A B = {2, 3, 4, 5} by
      rw [show f A B = {x | ∃ m ∈ A, ∃ n ∈ B, x = m + n} by rfl]
      rw [hA, hB]
      ext x
      simp
      <;> tauto
      <;> try { native_decide }
    ]

  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }