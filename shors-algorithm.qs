namespace Quantum.ShorsAlgorithm {

    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Measurement;

    
    @EntryPoint()
    operation Main () : (Int, Int) {
        //Start with a number to factor
        let numberToFactor = 21;

        //initial checks for primality and parity
        let initialChecks = InitialChecks(numberToFactor);
        if initialChecks == 0 {
            Message($"{numberToFactor} is prime. Its factors are 1 and {numberToFactor}");
            return (1, numberToFactor);
        } elif initialChecks == 1 {
            Message($"{numberToFactor} is even. Its factors are 2 and {numberToFactor/2}");
            return (2, numberToFactor/2);
        } else {
            Message($"{numberToFactor} neither prime nor even. Continuing with Shor's Algorithm.");
        }

        mutable bZero = 0;
        mutable bOne = 0;
        mutable period = 0;
        //start guessing from 3 to numberToFactor-1
        for guess in 2..numberToFactor-1 {
            let gcd = GreatestCommonDivisorI(guess, numberToFactor);
            if gcd != 1 {
                Message($"You got lucky! The guess {guess} has a gcd with {numberToFactor}. The factors are {gcd} and {numberToFactor / gcd}.");
                return (gcd, numberToFactor/gcd);
            }
            Message($"Looking for the period of {guess}^x mod {numberToFactor}...");
            set period = getPeriod(guess, numberToFactor);

            //final checks after period is acquired
            //only continue with period if it's even and satisfies conditions
            //if conditions not met, algorithm goes to next guess
            if period % 2 == 0 {
                Message($"Period {period} is even");
                if (ExpModI(guess, period/2, numberToFactor) != 1) and (ExpModI(guess, period/2, numberToFactor) != numberToFactor-1) {
                    Message($"Period {period} meets mod conditions");
                    set bZero = GreatestCommonDivisorI(numberToFactor, ExpModI(guess, period/2, numberToFactor)+1);
                    set bOne = GreatestCommonDivisorI(numberToFactor, ExpModI(guess, period/2, numberToFactor)-1);

                    if ((2 < bZero) and (bZero < numberToFactor) and (2 < bOne) and (bOne < numberToFactor)) {
                        Message($"Shor's Algorithm found these factors: {bZero} and {bOne}");
                        return (bZero, bOne);
                    } else {
                        Message($"Something went wrong...");
                    }
                } else {
                    Message($"{guess}^({period}/2) mod {numberToFactor} = 1 or {numberToFactor-1}. Go to next guess");
                }
            } else {
                Message($"Period {period} is odd, go to next guess");
            }  
        }

        //This should never happen, just a placeholder
        return (-1, -1);
    }

    function InitialChecks (
        numberToFactor : Int
    ) : Int {
        //number is prime, factors: 1. b
        if (ExpModI(2, numberToFactor-1, numberToFactor) == 1) {
            return 0;
        }
        //number is even, factors: b/2, 2
        if (numberToFactor%2 == 0) {
            return 1;
        }
        //if neither prime nor even
        return 2;
    }

    operation getPeriod (
        guess : Int,
        numberToFactor : Int
    ) : Int {
        //remainder and factor needed in loop
        mutable remainder = 0;
        mutable factor = 1;
        mutable bigCounter = 0;
        Message("Got to getPeriod()");
        //repeat until factor = period
        repeat {
            //keep doing quantum step until the numerator is not 0
            mutable (qNum, qDen) = (QuantumStep(guess, numberToFactor));
            Message($"qNum is {qNum} and qDen is {qDen}");
            if qNum == 0 {
                mutable smallCounter = 0;
                Message("qNum was measured as 0, retrying");
                repeat {
                    set (qNum, qDen) = (QuantumStep(guess, numberToFactor));
                    set smallCounter += 1;
                    Message($"smallCounter is {smallCounter}");
                } until ((qNum != 0) or (smallCounter == 3));
                Message($"After some repeats: qNum is {qNum} and qDen is {qDen}");
            }
            
            //get cDen as a factor of the period or the period itself
            mutable (cNum, cDen) = getConvergent(qNum, qDen, numberToFactor);
            Message($"cDen is {cDen}, which is a factor of the period");

            //add cDen as a factor
            set factor = cDen * factor / GreatestCommonDivisorI(cDen, factor);
            Message($"The greatest factor of the period is now {factor}");
            //get remainder aka result from guess^factor mod numberToFactor (if it's 1, then factor=period)
            set remainder = ExpModI(guess, factor, numberToFactor);
            Message($"The factor {factor} leaves a remainder of {remainder}");
            if factor == 0 {
                set bigCounter += 1;
            }
            Message($"bigCounter is {bigCounter}");
        } until ((remainder == 1) and (factor != 0)) or bigCounter == 3;

        //at this point, factor = period
        Message($"The period is {factor}");
        return factor;
    }

    //a is the guess
    //b is the numberToFactor
    operation QuantumStep (
        a : Int,
        b : Int
    ) : (Int, Int) {
        Message("Got to quantum step");
        //output size
        let m = Ceiling(Lg(IntAsDouble(b+1)));
        //input size
        let n = 2 * m;
        //|x> and |o>
        use (inputReg, outputReg) = (Qubit[n], Qubit[m]);
        //HAll input
        ApplyToEach(H, inputReg);
        //X last qubit of output to make it |1>
        X(outputReg[m-1]);
        //Quantum Modular Exponentiation
        for i in 0..n-1 {
            Message($"i = {i} / {n-1}");
            let c = ExpModI(a, 2^(n-1-i), b);
            Controlled MultiplyByModularInteger([inputReg[i]], (c, b, LittleEndian(outputReg)));
        }
        //Inverse QFT
        let inputAsBE = BigEndian(inputReg);
        Adjoint QFT(inputAsBE);
        Message("IQFT");
        //Measure |x> a.k.a. input
        let xPrime = MeasureInteger(BigEndianAsLittleEndian(inputAsBE));
        Message($"Integer Measured: {xPrime}");
        ResetAll(inputReg);
        ResetAll(outputReg);
        //return xPrime / 2^n fraction parts separately as tuple
        Message("End of Quantum Step");
        return (xPrime, 2^n);
    }

    function getConvergent (
        numerator : Int,
        denominator : Int,
        denominatorThreshold : Int
    ) : (Int, Int) {
        mutable a_i = 0;            // Coefficient
        mutable P_i = numerator;    // Numerator
        mutable Q_i = denominator;  // Denominator
        mutable r_i = 0;            // Remainder

        mutable n_i = 0;            // Convergent numerator
        mutable n_i1 = 1;           // Convergent numerator from previous iteration
        mutable n_i2 = 0;           // Convergent numerator from 2 iterations previous

        mutable d_i = 0;            // Convergent denominator
        mutable d_i1 = 0;           // Convergent denominator from previous iteration
        mutable d_i2 = 1;           // Convergent denominator from 2 iterations previous

        while true {
            // Calculate current coefficient, remainder, and convergent
            set a_i = P_i / Q_i;
            set r_i = P_i % Q_i;
            set n_i = a_i * n_i1 + n_i2;
            set d_i = a_i * d_i1 + d_i2;

            // Return if d_i > threshold
            if d_i > denominatorThreshold {
                Message($"Convergent: {n_i1} / {d_i1}");
                return (n_i1, d_i1);
            }

            // Return if r_i == 0
            if r_i == 0 {
                Message($"Convergent: {n_i} / {d_i}");
                return (n_i, d_i);
            }

            set P_i = Q_i;
            set Q_i = r_i;
            set n_i2 = n_i1;
            set n_i1 = n_i;
            set d_i2 = d_i1;
            set d_i1 = d_i;
        }

        // This should never happen
        return (-1, -1);
    }
}
