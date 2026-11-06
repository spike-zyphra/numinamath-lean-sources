import Mathlib

/- Suppose $50x$ is divisible by 100 and $kx$ is not divisible by 100 for all $k=1,2,\cdots, 49$ Find number of solutions for $x$ when $x$ takes values $1,2,\cdots 100$.
[list=1]
[*] 20
[*] 25
[*] 15
[*] 50
[/list] -/
theorem number_theory_63976 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 100 ∣ 50 * x ∧ ∀ k ∈ Finset.Icc 1 49, ¬100 ∣ k * x} = 20 := by 
  -- We aim to show that there are exactly 20 numbers in the range from 1 to 100 satisfying these conditions.
  have h : {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 100 ∣ 50 * x ∧ ∀ k ∈ Finset.Icc 1 49, ¬100 ∣ k * x}
    = Finset.filter (fun x => 100 ∣ 50 * x ∧ ∀ k ∈ Finset.Icc 1 49, ¬100 ∣ k * x) (Finset.Icc 1 100) := by
    ext
    aesop
  rw [h]
  -- Use simplification on the integers and positive conditions
  simp [Finset.filter]
  rfl