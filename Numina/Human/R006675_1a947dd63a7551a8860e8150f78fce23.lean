import Mathlib

/- Let $K_{max}$ be a given integer. During a math class, the teacher wrote a number $n$ on the board. Then, for each integer $d$ from $K_{max}$ down to 2 (i.e., $d \in \{K_{max}, K_{max}-1, \dots, 2\}$), a student claimed that $d$ divides the number $n$. Only two of these statements were false, and these two false statements corresponded to consecutive integers $x$ and $x-1$ (so $n$ is not divisible by $x$ and $n$ is not divisible by $x-1$, but $n$ is divisible by all other integers in the range $\{2, \dots, K_{max}\}$).

If $K_{max} = 18$, which two statements (i.e., which values $x$ and $x-1$) were incorrect? Show the answer is that the statements corresponding to 16 and 17 were incorrect. -/
theorem number_theory_639974
  {Kmax n : ℕ}
  (hKmax : Kmax = 18)
  (hn : n % 16 ≠ 0)
  (hn' : n % 17 ≠ 0)
  (hf : ∃ k, ∀d ∈ Finset.Icc 2 Kmax, d ∣ n ∨ d = k ∨ d = k + 1)
  : ∀d ∈ Finset.Icc 2 Kmax, d ∣ n ∨ d = 16 ∨ d = 17 :=
by
  intro d db
  simp at db
  rcases db
  subst hKmax
  rcases hf with ⟨k, kh⟩
  have : k = 16 := by
    have := kh 16 (by simp)
    rcases this with h|h|h
    . omega
    . omega
    have := kh 17 (by simp)
    rcases this with g|g|g
    . omega
    . omega
    . omega
  subst this
  interval_cases d
  <;> apply kh <;> simp
