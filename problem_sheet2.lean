/-  Math40001 : Introduction to university mathematics.

Problem Sheet 2, October 2019.

This is a Lean file. It can be read with the Lean theorem prover.

You can work on this file online at 
https://tinyurl.com/Lean-M40001-Example-Sheet-2

or you can install Lean and its maths library following the
instructions at
https://github.com/leanprover-community/mathlib#installation

There are advantages to installing Lean on your own computer
(for example it's faster), but it's more hassle than
just using it online.

In the below, delete "sorry" and replace it with some
tactics which prove the result.

-/

import data.real.basic -- need real numbers for Q5

-- Q1 prove that ∩ is symmetric
lemma question1 (Ω : Type) (X Y : set Ω) : X ∩ Y = Y ∩ X :=
begin
    ext a, split,
    intro h1, cases h1 with hx hy,
    split, exact hy, exact hx,
    intro h2, cases h2 with hy hx,
    split, exact hx, exact hy,
end

-- Q2 we define the set U
def U : set ℕ := {1, 2, 3, 4, 5}

/- and then five of the questions still make sense
   in type theory, and the other three don't.
   What I'm saying is that b,f,g would continue to be
   wrong even if you changed the numbers around, because
   the questions do not even typecheck: U only contains
   numbers, and b, f, g are asking if a non-number is
   in U.

   For the remaining five questions, if you think they're
   false then change `_true` to `_false` and add a ¬ in front.
-/

lemma question2a_true : 1 ∈ U :=
begin
  right,
  right,
  right,
  right,
  left,
  refl,
end

lemma question2c_true : {1} ⊆ U :=
begin
  intro h, intro h1,
  right, right, right, right, exact h1,
end

lemma question2d_true : {1, 2} ⊆ U :=
begin
  intro h,
  intro hs,
  right, right, right, exact hs,
end

lemma question2e_true : {1, 2, 1} ⊆ U :=
begin
  intro h,
  intro hs,
  right, right, right,
  cases hs,
  right, left, exact hs, exact hs,
end

lemma question2h_true : U ⊇ U :=
begin
  intro h, intro u, exact u,
end

-- question 3 defs
def A := {x : ℝ | x ^ 2 < 3}
def B := {x : ℝ | ∃ n : ℤ, x = n ∧ x ^ 2 < 3}
def C := {x : ℝ | x ^ 3 < 3}

-- like Q2, change _true to _false and put a ¬ in front
-- of the goal if you think it's false.

lemma question3a_false : ¬ (1 : ℝ)/2 ∈ A ∩ B :=
begin
  intro h,
  cases h with ha hb,
  have hnb : (1 : ℝ) / 2 ∉ B,
    sorry,
  exact hnb hb,
end

lemma question3b_true : (1 : ℝ)/2 ∈ A ∪ B :=
begin
  sorry
end

lemma question3c_true : A ⊆ C :=
begin
  sorry
end

lemma question3d_true : B ⊆ C :=
begin
  sorry
end

lemma question3e_true : C ⊆ A ∪ B :=
begin
  sorry
end

lemma question3f_true : (A ∩ B) ∪ C = (A ∪ B) ∩ C :=
begin
  sorry
end

-- Q4 set-up
variables (X Y : Type)
variable (P : X → Prop)
variable (Q : X → Prop)
variable (R : X → Y → Prop)

-- for Q4 you're going to have to change the right hand
-- side of the ↔ in the statement
-- of the lemma to the answer you think is correct.

lemma question4a : ¬ (∀ x : X, P x ∧ ¬ Q x) ↔ (∃ x : X, ¬ P x ∨ Q x) := -- change `true`!
begin
    split,
        intro h,
end

lemma question4b : ¬ (∃ x : X, (¬ P x) ∧ Q x) ↔ true := -- change `true`!
begin
  sorry
end

lemma question4c : ¬ (∀ x : X, ∃ y : Y, R x y) ↔ true := -- change `true`!
begin
  sorry
end

example (f : ℝ → ℝ) (x : ℝ) :
  ¬ (∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 → ∀ y : ℝ, abs (y - x) < δ → abs (f y -f x) < ε )
↔ -- change next line
true :=
begin
  sorry
end

-- change _true to _false in 5a, 5b if you think the opposite is true. 
lemma question5a_true : ∀ x : ℝ, ∃ y : ℝ, x + y = 2 :=
begin
  sorry
end

lemma question5b_true : ∃ y : ℝ, ∀ x : ℝ, x + y = 2 :=
begin
  sorry
end 

-- similarly for Q6 -- change _true to _false and add in a negation if you 
-- want to prove that the proposition in the question is false.
lemma question6a_true : ∃ x ∈ (∅ : set ℕ), 2 + 2 = 5 :=
begin
  sorry
end

lemma question6b_true : ∀ x ∈ (∅ : set ℕ), 2 + 2 = 5 :=
begin
  sorry
end 
