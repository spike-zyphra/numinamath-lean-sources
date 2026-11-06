import Mathlib

open Real Set
open scoped Real

/-
194. For what real $a, b, c$ is the equality $|a x+b y+c z|+|b x+c y+a z|+|c x+a y+b z|=$
$$
=|x|+|y|+|z|
$$

true for all real $x, y, z$?
-/

set_option maxHeartbeats 600000
theorem algebra_277342 (a b c:ℝ):
(∀x:ℝ, ∀y:ℝ, ∀z:ℝ, |a*x+b*y+c*z| + |b*x+c*y+a*z| + |c*x+a*y+b*z| = |x|+|y|+|z|) 
↔ 
((a=1∧b=0∧c=0)∨(a=-1∧b=0∧c=0)∨(a=0∧b=1∧c=0)∨(a=0∧b=-1∧c=0)∨(a=0∧b=0∧c=1)∨(a=0∧b=0∧c=-1)) := by
  
  constructor
  --From left to right.
  intro h

  --Let x = y = z = 1, we have |a+b+c| = 1.
  have abcabs: |a+b+c| = 1 := by 
    specialize h 1 1 1
    simp at h
    have : b+c+a = a+b+c := by linarith
    rw [this] at h
    have : c+a+b = a+b+c := by linarith
    rw [this] at h
    ring_nf at h
    field_simp at h
    exact h
  --Let x = 1 and y = z = 0. We have |a|+|b|+|c| = 1.
  have aabsbabscabs : |a|+|b|+|c| = 1 := by 
    specialize h 1 0 0 
    simp at h
    exact h
  --Let x = 1, y = -1, z = 0. We have |a-b|+|b-c|+|c-a| = 2.
  have mabs: |a-b|+|b-c|+|c-a| = 2 := by 
    specialize h 1 (-1) 0 
    simp at h
    ring_nf at h ⊢
    exact h

  --From the above equations, we have  $a$, $b$, $c$ must be of the same sign (unless some of them is/are equal to $0$). Also The equality $|a-b|=|a|+|b|$ holds only if $a$ and $b$ are of opposite signs (unless some of them are equal to $0$). Similarly, $b$ and $c$ have opposite signs, and $c$ and $a$ have opposite signs.
  --We enumerate all possible cases.
  have t1: 2 = |a+ (-b)| + |b + (-c)| + |c + (-a)| := by ring_nf at mabs ⊢; exact mabs.symm
  have amb: |a - b| ≤ |a|+|b| := by exact abs_sub a b
  have : a - b = a + (-b) := by linarith
  rw [this] at amb
  have : |b| = |-b| := by simp
  rw [this] at amb
  have bmc: |b - c| ≤ |b|+|c| := by exact abs_sub b c
  have : b - c = b + (-c) := by linarith
  rw [this] at bmc
  have : |c| = |-c| := by simp
  rw [this] at bmc
  have cma: |c - a| ≤ |c|+|a| := by exact abs_sub c a
  have : c - a = c + (-a) := by linarith
  rw [this] at cma
  have : |a| = |-a| := by simp
  rw [this] at cma
  have : (|a|+|-b|) + (|b|+|-c|) + (|c|+|-a|) = 2 := by simp; linarith

  have sab: |a + (-b)| = |a| + |-b| := by linarith
  rw [abs_add_eq_add_abs_iff] at sab
  have sbc: |b + (-c)| = |b| + |-c| := by linarith
  rw [abs_add_eq_add_abs_iff] at sbc
  have sca: |c + (-a)| = |c| + |-a| := by linarith
  rw [abs_add_eq_add_abs_iff] at sca
  
  simp at sab sbc sca
  
  rcases sab with sab | sab

  rcases sbc with sbc | sbc
  
  rcases sca with sca | sca
  have ae: a = 0 := by linarith
  have be: b = 0 := by linarith
  have ce: c = 0 := by linarith
  rw [ae,be,ce] at abcabs
  norm_num at abcabs
  have be : b=0 := by linarith
  rw [be] at abcabs aabsbabscabs mabs
  simp at abcabs aabsbabscabs mabs
  have : |a+c| = |a|+|c| := by linarith
  rw [abs_add_eq_add_abs_iff] at this
  rcases this with h | h
  have ce: c=0 := by linarith
  simp [ce] at abcabs
  have : a = 1 ∨ a=-1 := by exact eq_or_eq_neg_of_abs_eq abcabs
  tauto
  have : a = 0:= by linarith
  simp [this] at aabsbabscabs mabs
  have : c = 1 ∨ c=-1 := by exact eq_or_eq_neg_of_abs_eq aabsbabscabs
  tauto
  
  rcases sca with sca | sca
  have ae : a = 0 := by linarith
  rw [ae] at abcabs aabsbabscabs mabs
  simp at abcabs aabsbabscabs mabs
  have : |b+c| = |b|+|c| := by linarith
  rw [abs_add_eq_add_abs_iff] at this
  rcases this with h | h
  have be: b=0 := by linarith
  rw [be] at abcabs; 
  simp at abcabs
  have ce: c = 1 ∨ c=-1 := by exact eq_or_eq_neg_of_abs_eq abcabs
  tauto
  have : c = 0 := by linarith
  simp [this] at aabsbabscabs mabs
  have : b = 1 ∨ b=-1 := by exact eq_or_eq_neg_of_abs_eq aabsbabscabs
  tauto
  have ce : c = 0 := by linarith
  simp [ce] at abcabs aabsbabscabs mabs
  have : |a+b| = |a|+|b| := by linarith
  rw [abs_add_eq_add_abs_iff] at this
  rcases this with h | h
  have be: b = 0 := by linarith
  simp [be] at abcabs;
  have ae: a = 1 ∨ a = -1 := by exact eq_or_eq_neg_of_abs_eq abcabs
  tauto
  have : a = 0 := by linarith
  simp [this] at aabsbabscabs mabs
  have : b = 1 ∨ b=-1 := by exact eq_or_eq_neg_of_abs_eq aabsbabscabs
  tauto

  rcases sbc with sbc | sbc

  rcases sca with sca | sca

  have ce :  c = 0 := by linarith
  simp [ce] at abcabs aabsbabscabs mabs
  have : |a+b| = |a|+|b| := by linarith
  rw [abs_add_eq_add_abs_iff] at this
  rcases this with h | h
  have ae : a = 0:= by linarith
  simp [ae] at abcabs;
  have be: b = 1 ∨ b=-1 := by exact eq_or_eq_neg_of_abs_eq abcabs
  tauto
  have be : b = 0 := by linarith
  simp [be] at abcabs aabsbabscabs mabs
  have : a = 1 ∨ a=-1 := by exact eq_or_eq_neg_of_abs_eq aabsbabscabs
  tauto
  have ae : a = 0:= by linarith
  simp [ae] at abcabs aabsbabscabs
  have : |b+c| = |b|+|c| := by linarith
  rw [abs_add_eq_add_abs_iff] at this
  rcases this with h | h
  have ce: c = 0 := by linarith
  simp [ce] at abcabs;
  have be: b = 1 ∨ b=-1 := by exact eq_or_eq_neg_of_abs_eq abcabs
  tauto
  have  be: b = 0 := by linarith
  simp [be] at abcabs aabsbabscabs mabs
  have : c = 1 ∨ c=-1 := by exact eq_or_eq_neg_of_abs_eq aabsbabscabs
  tauto

  rcases sca with sca | sca
  have be : b = 0 := by linarith
  simp [be] at abcabs aabsbabscabs mabs
  have : |a+c| = |a|+|c| := by linarith
  rw [abs_add_eq_add_abs_iff] at this
  rcases this with h | h
  have ae : a = 0 := by linarith
  simp [ae] at abcabs;
  have ce: c = 1 ∨ c=-1 := by exact eq_or_eq_neg_of_abs_eq abcabs
  tauto
  have ce : c = 0 := by linarith
  simp [ce] at abcabs aabsbabscabs mabs
  have : a = 1 ∨ a=-1 := by exact eq_or_eq_neg_of_abs_eq aabsbabscabs
  tauto
  have ae : a = 0 := by linarith
  have be : b = 0 := by linarith
  have ce : c = 0 := by linarith
  simp [ae,be,ce] at abcabs
  

  --From right to left. Simple caclulation.
  intro h
  rcases h with ⟨ae,be,ce⟩ | ⟨ae,be,ce⟩ | ⟨ae,be,ce⟩ | ⟨ae,be,ce⟩ | ⟨ae,be,ce⟩ | ⟨ae,be,ce⟩ <;>
  intro x y z <;>
  simp [ae,be,ce] <;>
  linarith