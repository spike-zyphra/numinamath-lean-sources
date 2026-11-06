import Mathlib

/- A group of $N$ students, where $N < 50$, is on a field trip. If their teacher puts them in groups of 8, the last group has 5 students. If their teacher instead puts them in groups of 6, the last group has 3 students. What is the sum of all possible values of $N$? -/
theorem number_theory_23133 :
    ∑ n in (Finset.Ico 1 50).filter (fun n => n % 8 = 5 ∧ n % 6 = 3), n = 66 := by
  have h : (Finset.Ico 1 50).filter (fun n => n % 8 = 5 ∧ n % 6 = 3) = {21, 45} := by
    ext n
    simp
    apply Iff.intro
    . rintro ⟨⟨h₀, h₁⟩, h₂, h₃⟩
      omega
    . rintro (h | h)
      omega
      omega
  rw [h]
  norm_num
