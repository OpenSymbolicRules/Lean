import OSR.IntegrationSinSquare

example : OSR.IntegrationNum1.rubi4111r11Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinSquare_real
example : OSR.IntegrationNum1.rubi4111r11Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinSquare_complex

example : OSR.IntegrationNum1.rubi4111r6Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinLinear_real
example : OSR.IntegrationNum1.rubi4111r6Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinLinear_complex

example : OSR.IntegrationNum1.rubi4111r2Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinHalfAngle_real
example : OSR.IntegrationNum1.rubi4111r2Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinHalfAngle_complex

example : OSR.IntegrationNum1.rubi417r1Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinQuarticProduct_real
example : OSR.IntegrationNum1.rubi417r1Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinQuarticProduct_complex
example : OSR.IntegrationNum1.rubi417r10Nondeg.Holds .real :=
  OSR.IntegrationSinSquare.sinQuarticSquare_real
example : OSR.IntegrationNum1.rubi417r10Nondeg.Holds .complex :=
  OSR.IntegrationSinSquare.sinQuarticSquare_complex
