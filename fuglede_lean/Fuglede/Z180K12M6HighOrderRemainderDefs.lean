import Fuglede.Z180K12Projection36Remainders3_12

/-! # Explicit projected remainder forms for the high-order `k = 12` sieve -/

namespace Fuglede

namespace Z180K12HighOrder

def projection36Phi3R0 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 0 - projection36Count12 b 2 +
    projection36Count12 b 3 - projection36Count12 b 5 +
    projection36Count12 b 6 - projection36Count12 b 8 +
    projection36Count12 b 9 - projection36Count12 b 11

def projection36Phi3R1 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 1 - projection36Count12 b 2 +
    projection36Count12 b 4 - projection36Count12 b 5 +
    projection36Count12 b 7 - projection36Count12 b 8 +
    projection36Count12 b 10 - projection36Count12 b 11

def projection36Phi9R0 (b : Fin 36 → Int) : Int :=
  b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33
def projection36Phi9R1 (b : Fin 36 → Int) : Int :=
  b 1 - b 7 + b 10 - b 16 + b 19 - b 25 + b 28 - b 34
def projection36Phi9R2 (b : Fin 36 → Int) : Int :=
  b 2 - b 8 + b 11 - b 17 + b 20 - b 26 + b 29 - b 35
def projection36Phi9R3 (b : Fin 36 → Int) : Int :=
  b 3 - b 6 + b 12 - b 15 + b 21 - b 24 + b 30 - b 33
def projection36Phi9R4 (b : Fin 36 → Int) : Int :=
  b 4 - b 7 + b 13 - b 16 + b 22 - b 25 + b 31 - b 34
def projection36Phi9R5 (b : Fin 36 → Int) : Int :=
  b 5 - b 8 + b 14 - b 17 + b 23 - b 26 + b 32 - b 35

def projection36Phi12R0 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 0 - projection36Count12 b 4 -
    projection36Count12 b 6 + projection36Count12 b 10

def projection36Phi12R1 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 1 - projection36Count12 b 5 -
    projection36Count12 b 7 + projection36Count12 b 11

def projection36Phi12R2 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 2 + projection36Count12 b 4 -
    projection36Count12 b 8 - projection36Count12 b 10

def projection36Phi12R3 (b : Fin 36 → Int) : Int :=
  projection36Count12 b 3 + projection36Count12 b 5 -
    projection36Count12 b 9 - projection36Count12 b 11

def projection36Phi18R0 (b : Fin 36 → Int) : Int :=
  b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33
def projection36Phi18R1 (b : Fin 36 → Int) : Int :=
  b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34
def projection36Phi18R2 (b : Fin 36 → Int) : Int :=
  b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35
def projection36Phi18R3 (b : Fin 36 → Int) : Int :=
  b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33
def projection36Phi18R4 (b : Fin 36 → Int) : Int :=
  b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34
def projection36Phi18R5 (b : Fin 36 → Int) : Int :=
  b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35

def projection36Phi36R0 (b : Fin 36 → Int) : Int := b 0 - b 12 - b 18 + b 30
def projection36Phi36R1 (b : Fin 36 → Int) : Int := b 1 - b 13 - b 19 + b 31
def projection36Phi36R2 (b : Fin 36 → Int) : Int := b 2 - b 14 - b 20 + b 32
def projection36Phi36R3 (b : Fin 36 → Int) : Int := b 3 - b 15 - b 21 + b 33
def projection36Phi36R4 (b : Fin 36 → Int) : Int := b 4 - b 16 - b 22 + b 34
def projection36Phi36R5 (b : Fin 36 → Int) : Int := b 5 - b 17 - b 23 + b 35
def projection36Phi36R6 (b : Fin 36 → Int) : Int := b 6 + b 12 - b 24 - b 30
def projection36Phi36R7 (b : Fin 36 → Int) : Int := b 7 + b 13 - b 25 - b 31
def projection36Phi36R8 (b : Fin 36 → Int) : Int := b 8 + b 14 - b 26 - b 32
def projection36Phi36R9 (b : Fin 36 → Int) : Int := b 9 + b 15 - b 27 - b 33
def projection36Phi36R10 (b : Fin 36 → Int) : Int := b 10 + b 16 - b 28 - b 34
def projection36Phi36R11 (b : Fin 36 → Int) : Int := b 11 + b 17 - b 29 - b 35

end Z180K12HighOrder

end Fuglede
