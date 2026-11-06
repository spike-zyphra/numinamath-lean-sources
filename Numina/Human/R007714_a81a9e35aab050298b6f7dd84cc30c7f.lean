import Mathlib

/- PROBLEM: Let A, B, C and D be the vertices of a regular tetrahedron, each of whose edges measures 1 meter. 
A bug, starting from vertex A, observes the following rule: at each vertex it chooses one of the three 
edges meeting at that vertex, each edge being equally likely to be chosen, and crawls along that edge to 
the vertex at its opposite end. Let p=n/729 be the probability that the bug is at vertex A when it has 
crawled exactly 7 meters. Find the value of n. -/
theorem combinatorics_94732 
  (P : ℕ → ℝ) 
  (hP0 : P 0 = 1) 
  (hP : ∀ k : ℕ, P (k+1) = (1 - P k)/3) : 
  P 7 * 729 = 182 := by {
  rw [hP, hP, hP, hP, hP, hP, hP, hP0]
  norm_num
}