abstract sig Light {
   var color : one Color,
   var car : lone Car
} {
   always (some car implies eventually color = GREEN)
}

sig Car {}
enum Color {GREEN, RED}

// concrete traffic lights in the scenario
one sig LightA, LightB extends Light {}

pred crash {
   LightA.color = RED and LightB.color = RED
}

fact initiallyBothRed {
   Light.color = GREEN
}

assert neverCrash {always not crash}

check neverCrash
