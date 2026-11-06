import Mathlib

/-
13. (6 points) $a, b, c$ are three distinct natural numbers, and $a+b+c=48$, then the maximum product of $a, b, c$ is
-/

theorem number_theory_186204 :
IsGreatest {x:ℕ | ∃a:ℕ, ∃b:ℕ, ∃c:ℕ, a≠b ∧ a≠c ∧ b≠c ∧ a+b+c = 48 ∧ a*b*c = x} 4080 := by

  unfold IsGreatest upperBounds
  simp

  constructor

  use 15, 16
  simp
  use 17
  simp

  intro x a b aneb c anec bnec hsum hmul
  rw [← hmul]
  
  --wlog we assume that a<b<c.
  wlog alb : a < b
  have bla : b < a := by omega
  have : b * a * c ≤ 4080 := by 
    apply this
    omega
    exact bnec
    exact anec
    omega
    have : b*a*c = x := by linarith
    exact this
    exact bla
  nlinarith

  wlog blc : b < c
  have clb : c < b := by omega
  by_cases alc : a < c
  have : a * c * b ≤ 4080 := by
    apply this
    omega
    exact aneb
    omega
    linarith
    have : a*c*b = x := by linarith
    exact this
    exact alc
    exact clb
  nlinarith
  have cla : c < a := by omega
  have : c * a * b ≤ 4080 := by
    apply this
    omega
    omega
    exact aneb
    linarith
    have : c * a * b = x := by linarith
    exact this
    exact cla
    exact alb
  nlinarith

  --Then we can have a bound for a b and c. We just enuremate the possibilities.
  have ale15 : a ≤ 15 := by omega
  have ble23 : b ≤ 23 := by omega
  have cle47 : c ≤ 47 := by omega
  have cge17 : 17 ≤ c := by omega
  interval_cases a <;>
  interval_cases b <;>
  omega