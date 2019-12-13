-- Lean is based on a dependent type theory
    -- a system known as the Calculus of Constructions

-- Simple Type Theory
    -- Set theory is appealing as everything is a set.
    -- However, when dealing with formal theorem proving, it is better to have an infrastructure that keeps track of objects.
    -- Every expression in Type Theory has an associated type.
    -- A boolean variable is a variable whos value is either true or false.

constant m : nat
#check m
constants k l : ℕ 
#check k

-- In Lean, types themselves have a type.

#check ℕ 
#check Type
#check Type 2

constants α β γ : Type
constant f : α → β
constant g : β → γ
constant b : β
constant h : γ  → γ  × γ  
#check λ x : α, x -- α → α
#check λ x : α, b -- α → β
#check λ x : α, g (f x) -- α → γ

-- We can also, in general, leave off the type annotations on the variable

#check λ x, g (f x)
#check λ x, h (g (f x))

-- These functions can be combined

#check λ (b : β) (x : α), x
#check λ (g : β → γ) (f : α → β) (x : α), g (f x) -- (β → γ) → (α → β) → α → γ

-- You can combine these expressions such that

#check λ (α β : Type) (b : β) (x : α), x
#check λ (α β γ : Type) (g : β → γ) (f : α → β) (x : α), g (f x)
#check λ (ξ ζ μ : Type) (P : ξ → ζ) (Q : ζ → μ) (R : μ → ξ) (x : ξ), R (Q (P x))

-- The naming of the variables is simply a name resulting 
-- λ (b : β) (x : α) to be considered the same as λ (u : β) (z : α)
-- Formally, the expressions that are the same up to a renaming of bound variables are called
    -- Alpha Equivalent

-- The command #reduce tells Lean to evaluate an expression by reducing it to normal form.

constants c d : ℕ

#print "This command prints things as expected!"
#reduce (c, d).1
#reduce (c, d).2

-- How terms are reduced will be explained at #.
    -- However, it is important to keep in mind that every term has a computational behavior and a notion of reduction.
    -- If two terms are reduced to the same value then they are Definitely Equal,
    -- i.e. considered to be the same by the underlying logical framework.

-- The def command can be used to define new objects.
    -- The def command has general form def name : (type) : λ variables := expression.
    -- Or def name (variables : type) := expression

def double : ℕ → ℕ := λ x, x + x
#print double
#check double 3
#reduce double 3

def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)
def Do_twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ f x, (f x)
def composite (f g : ℕ → ℕ) (x : ℕ) := f (g x)

#reduce Do_twice do_twice double 3

-- A local definition can be introduced with let a := t1 in t2 which replaces every occurrence of a in t2 by t1

def t (x : ℕ) :=
    let y := x + x in y * y

#reduce t 2

def do_thrice (x : ℕ) := x + x + x

def do_many (x : ℕ) :=
    let y := x * x in do_thrice y

#reduce do_many 3

-- Variables can be declared locally as we have done above or globally.
    -- To declare a variable globally we use the variable and variables commands.

variable (j : ℕ)
def Do_thrice := j + j + j
#reduce Do_thrice 3

-- Sometimes, it is useful to limit the scope of a variable within a limited space.
    -- To achieve this we use the command section

section exmp
    variable (x :ℕ)
end exmp

-- Lean provides us with the ability to group definitions into nested, hierarchical namespaces.

namespace foo
  def a : ℕ := 5

  #print "inside foo"

  #check a
end foo

#check foo.a -- Identifier within the namespace has prefix "foo".
open foo -- Opens foo.
#check a

-- Lean can have types that are dependent on parameters.

universe u
constant cons : Π α : Type u, α → list α → list α 

-- ???

variables p q r s : Prop
theorem t2 (h1 : q → r) (h2 : p → q) : p → r :=
begin
    assume h3 : p,
    exact h1 (h2 h3),
end

-- Tactics

-- intros is the plural of intro
-- revert is kinda the inverse of intro

example (x : ℕ) : x = x :=
begin
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y,
  -- goal is y : ℕ ⊢ y = y
  reflexivity
end

-- arbitary expressions can be generalized using genralize

example : 3 = 3 :=
begin
  generalize : 3 = x,
  -- goal is x : ℕ ⊢ x = x,
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y, reflexivity
end

-- use this when confused
-- set_option pp.notation false

-- show what simp did
-- set_option trace.simplify.rewrite true