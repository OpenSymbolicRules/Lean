import OSR.IntegrationSinSquare

example : OSR.IntegrationNum1.rubi4111r11Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinSquare_real
example : OSR.IntegrationNum1.rubi4111r11Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinSquare_complex

example : OSR.IntegrationNum1.rubi4111r6Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinLinear_real
example : OSR.IntegrationNum1.rubi4111r6Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinLinear_complex
