import Mathlib

open Nat ZMod
/-Given the sequence ${{a}_{n}}$ satisfies: ${{a}_{n}}={{(\sqrt{2}+1)}^{n}}-{{(\sqrt{2}-1)}^{n}}$ ($n\in {{\mathbf{N}}^{*}}$), where $[x]$ denotes the greatest integer not exceeding the real number $x$, then the units digit of $[{{a}_{2017}}]$ is ( ).

A: $2$
B: $4$
C: $6$
D: $8$
-/

noncomputable def an (n : ℕ): ℝ := ((Real.sqrt 2 + 1) ^ n - (Real.sqrt 2 - 1) ^ n)

noncomputable def bn (n : ℕ): ℝ := an (2 * n - 1)

-- Periodicity of 6
lemma bn_period : ∀ (k1 k2 : ℕ), k1 = (k2 : ZMod 6) → 
(Nat.floor (bn (k1) ): ZMod 10) = (Nat.floor (bn k2) : ZMod 10) := by sorry

theorem number_theory_628145 : Nat.floor (an 2017) = (2 : ZMod 10) := by 
  have : bn 1009 = an 2017 := by 
    unfold bn
    norm_num
  rw [← this]
  have : Nat.floor (bn 1009) = (Nat.floor (bn 1) : ZMod 10) := by 
    exact bn_period 1009 1 (by decide)
  rw [this]
  unfold bn an
  ring_nf
  simp




