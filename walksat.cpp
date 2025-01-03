#include <iostream>
#include <vector>
#include <unordered_set>
#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <sstream>
#include <cmath>
#include <sstream>
using namespace std;

// Initialization of Global variables
int NumberofProblems; // Number of 3-SAT problems to generate
int NumberofVariables; // Number of variables in each problem
int NumberofClauses; // Number of clauses in each problem
int maxTries; // Maximum attempts for WalkSAT
int maxFlips; // Maximum variable flips per try
double negativeProbability; // Probability of generating negative literals
double p; // Probability for random walk in WalkSAT
double a; // Parameter for semi-infinite initial state creation

////////////////////////////////////////////////////////////////////////
/////////////////////////3SAT-PROBLEM-GENERATOR/////////////////////////
////////////////////////////////////////////////////////////////////////

//This function generates a random literal (positive or negative variable)
int generateLiteral() {
    int literal = rand() % NumberofVariables + 1; //We generate a random variable index between 1 and NumberofVariables
    if (static_cast < double > (rand()) / RAND_MAX < negativeProbability) { //Randomly decide the literal (negative-positive)
        literal = -literal; //Make literal negative with probability based on negativeProbability
    }
    return literal; // Return the generated literal
}

//This function aims into checking if a clause contains contradictions or duplicates
//In order to avoid them
bool isClauseValid(const vector < int > & clause) {
    unordered_set < int > checked; //Here we declare a set named checked in order to track checked literals
    for (int literal: clause) {
        if (checked.count(-literal) || checked.count(literal)) { //We check for contradiction (x and ¬x) or duplication (x and x)
            return false;
        }
        checked.insert(literal); // Add literal to checked set
    }
    return true; // Clause is valid
}

//In this function we convert clause into string in order to check if it is unique
string clauseToString(const vector < int > & clause) {
    //We Sort the clause in order to represent it
    vector < int > sortedClause = clause;
    sort(sortedClause.begin(), sortedClause.end());
    //We construct the string
    stringstream clauseStream;
    for (int literal: sortedClause) {
        clauseStream << literal << " ";
    }
    return clauseStream.str(); // Return the string representation of the clause
}

//In this function we practically generate a random 3-SAT problem according to the instructions of the exercise
vector < vector < int >> generate3SATProblem() {
    vector < vector < int >> clauses(NumberofClauses, vector < int > (3)); // Create a vector for clauses, each one of the clauses has 3 literals
    unordered_set < string > uniqueClauses; //Here we create a set named uniqueClauses in order to store the unique clauses

    // Counter to check if we have reached the desired number of clauses
    int clauseCount = 0;
    while (clauseCount < NumberofClauses) {
        vector < int > clause(3); // Generate a clause with three random literals
        for (int i = 0; i < 3; ++i) {
            clause[i] = generateLiteral(); // Generate each literal
        }
        // Skip invalid or duplicated clauses, check if the clause is valid
        if (!isClauseValid(clause)) continue;
        string clauseStr = clauseToString(clause);
        if (uniqueClauses.count(clauseStr)) continue;
        clauses[clauseCount] = clause; // Store the valid and unique clause into uniqueClauses set
        uniqueClauses.insert(clauseStr);
        clauseCount++;
    }

    return clauses; // Return the generated clauses
}

// Displays the 3-SAT problems
// "(" Start of clause ... ")" End of clause
// We use "¬" for negative literals
// ∨ is logical OR between literals ... ∧ is logical AND between clauses
void display3SATProblem(const vector < vector < int >> & clauses) {
    for (size_t i = 0; i < clauses.size(); ++i) {
        cout << "(";
        for (size_t j = 0; j < clauses[i].size(); ++j) {
            cout << (clauses[i][j] > 0 ? "x" : "¬x") << abs(clauses[i][j]);
            if (j < clauses[i].size() - 1) cout << " ∨ ";
        }
        cout << ")";
        if (i < clauses.size() - 1) cout << " ∧ ";
    }
    cout << endl;
}

//In this function we practically aim into getting valid input from user as far as the parameters are concerned
//We check for input validation at variables like (NumberofProblems, NumberofVariables, NumberofClauses, negativeProbability,maxFlips, maxTries, p)
bool getValidInput() {

    do {
        cout << "Enter number of problems: ";
        cin >> NumberofProblems;
    } while (NumberofProblems <= 0);

    do {
        cout << "Enter number of variables (N): ";
        cin >> NumberofVariables;
    } while (NumberofVariables <= 0);

    do {
        cout << "Enter number of clauses (C): ";
        cin >> NumberofClauses;
    } while (NumberofClauses <= 0);

    do {
        cout << "Enter negative literal probability (0-1): ";
        cin >> negativeProbability;
    } while (negativeProbability < 0 || negativeProbability > 1);

    do {
        cout << "Enter maxTries: ";
        cin >> maxTries;
    } while (maxTries <= 0);

    do {
        cout << "Enter maxFlips: ";
        cin >> maxFlips;
    } while (maxFlips <= 0);

    do {
        cout << "Enter parameter p (0-1): ";
        cin >> p;
    } while (p < 0 || p > 1);

    do {
        cout << "Enter parameter a for semi-infinite initial state creation: ";
        cin >> a;
    } while (a <= 0 || a >= 1);

    return true; // Return true if all inputs are valid
}
/////////////////////////////////////////////////////////////////////////
/////////////////////////3SAT-PROBLEM-GENERATOR//////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////WALKSAT/////////////////////////////////
/////////////////////////////////////////////////////////////////////////

//In this function we generate random initial assignments
vector < bool > generateRandomAssignment() {
    vector < bool > assignment(NumberofVariables); //Here we hold variable assignments
    for (int i = 0; i < NumberofVariables; i++) {
        assignment[i] = rand() % 2; // Randomly assign true/false
    }
    return assignment; // Return the random assignment
}

//This function evaluates if a clause is satisfied by the current assignment (True/False)
bool evaluateClause(const vector < int > & clause, const vector < bool > & assignment) {
    for (int literal: clause) {
        int variableIndex = abs(literal) - 1;
        bool variableValue = assignment[variableIndex]; // Get current value of the variable
        if (literal < 0) { //We make the variableValue negative if the literal is negative
            variableValue = !variableValue;
        }

        if (variableValue) { // If any literal evaluates to true then the clause is satisfied
            return true;
        }
    }
    return false;
}

//In this function we count the number of satisfied clauses in our problem
int countSatisfiedClauses(const vector < vector < int >> & clauses, const vector < bool > & assignment) {
    int count = 0;
    for (const auto & clause: clauses) {
        if (evaluateClause(clause, assignment)) count++;
    }
    return count;
}

// Check if all clauses are satisfied
bool isSatisfied(const vector < vector < int >> & clauses,
    const vector < bool > & assignment) {
    return countSatisfiedClauses(clauses, assignment) == clauses.size();
}

//In this function we select variable to flip using WalkSAT heuristic
int selectVariable(const vector < int > & clause, vector < bool > & assignment, const vector < vector < int >> & clauses) {
    vector < int > improvedVariables; // Variables that improve the solution
    int currentSatisfied = countSatisfiedClauses(clauses, assignment); // Count currently satisfied clauses

    for (int literal: clause) { // Find variables that improve solution when flipped
        int variable = abs(literal) - 1;
        assignment[variable] = !assignment[variable]; // Flip the variable
        int newSatisfied = countSatisfiedClauses(clauses, assignment); // Count satisfied clauses after flip
        assignment[variable] = !assignment[variable]; // Restore original assignment

        if (newSatisfied > currentSatisfied) {
            improvedVariables.push_back(variable); // Add variable to improving variables if it practically improves the clauses
        }
    }

    // If improving variables exist then choose randomly from them
    if (!improvedVariables.empty()) {
        return improvedVariables[rand() % improvedVariables.size()]; // Return variable that improves our clauses randomly
    }

    // Random walk with probability p
    if (static_cast < double > (rand()) / RAND_MAX < p) {
        return abs(clause[rand() % clause.size()]) - 1; // Randomly select a variable from the clause
    }

    // Choose variable that breaks fewest clauses
    // Initialize variables
    int bestVariable = abs(clause[0]) - 1;
    int minimumBreakCount = NumberofClauses;

    for (int literal: clause) {
        int variable = abs(literal) - 1;
        assignment[variable] = !assignment[variable];
        int breaks = NumberofClauses - countSatisfiedClauses(clauses, assignment); // Calculate how many clauses are broken by this flip
        assignment[variable] = !assignment[variable]; // Restore original assignment

        if (breaks < minimumBreakCount) {
            minimumBreakCount = breaks;
            bestVariable = variable; // Update best variable in order to flip
        }
    }
    return bestVariable; // Return the variable that breaks the fewest clauses
}

// WalkSAT algorithm implementation
vector<bool> walkSAT(const vector<vector<int>>& clauses) {
    int bestCost = NumberofClauses;
    vector<bool> bestAssignment;

    for (int try_count = 0; try_count < maxTries; try_count++) {
        vector<bool> assignment = generateRandomAssignment(); // A := randomly chosen assignment of the variables in a

        for (int flip_count = 0; flip_count < maxFlips; flip_count++) {
            int currentCost = NumberofClauses - countSatisfiedClauses(clauses, assignment);
            if (currentCost < bestCost) {
                bestCost = currentCost;
                bestAssignment = assignment;
            }

            if (currentCost == 0) {
                cout << "Solution found with cost: 0" << endl;
                return assignment; // if A satisfies a then return (A)
            }

            vector<int> unsatisfiedClauses;
            for (size_t i = 0; i < clauses.size(); i++) {
                if (!evaluateClause(clauses[i], assignment)) {
                    unsatisfiedClauses.push_back(i); // c := randomly chosen unsatisfied clause
                }
            }

            int clauseIndex = unsatisfiedClauses[rand() % unsatisfiedClauses.size()];
            int varToFlip = selectVariable(clauses[clauseIndex], assignment, clauses); // x := choose a variable in c using a heuristic
            assignment[varToFlip] = !assignment[varToFlip]; // flip value of x in A
        }
    }

    if (!bestAssignment.empty()) {
        cout << "Best state found with cost: " << bestCost << endl;
        return bestAssignment;
    } else {
        cout << "No solution found after maximum tries. Best cost: " << bestCost << endl;
        return {}; // return (“No model found”)
    }
}

//This function displays the solution
void displayAssignment(const vector < bool > & assignment) {
    cout << "Solution: ";
    for (size_t i = 0; i < assignment.size(); i++) {
        cout << "x" << (i + 1) << "=" << assignment[i] << " "; // Display the assignment of each variable
    }
    cout << endl;
}
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////WALKSAT/////////////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
//////////////////////////////WALKSATWITH-A//////////////////////////////
/////////////////////////////////////////////////////////////////////////


//In this function we generate random initial assignments with semi-infinite initial state creation
vector<bool> generateRandomAssignmentWalkWithA() {
    vector<bool> assignment(NumberofVariables); //Here we hold variable assignments
    for (int i = 0; i < NumberofVariables; i++) {
        assignment[i] = static_cast<double>(rand()) / RAND_MAX < a; // Assign true/false based on parameter 'a'
    }
    return assignment; // Return the random assignment
}

// WalkSAT algorithm implementation with (a)
vector<bool> walkSATwithA(const vector<vector<int>>& clauses) {
    int bestCost = NumberofClauses;
    vector<bool> bestAssignment;

    for (int try_count = 0; try_count < maxTries; try_count++) {
        vector<bool> assignment = generateRandomAssignmentWalkWithA(); // A := randomly chosen assignment of the variables in a

        for (int flip_count = 0; flip_count < maxFlips; flip_count++) {
            int currentCost = NumberofClauses - countSatisfiedClauses(clauses, assignment);
            if (currentCost < bestCost) {
                bestCost = currentCost;
                bestAssignment = assignment;
            }

            if (currentCost == 0) {
                cout << "Solution found with cost: 0" << endl;
                return assignment; // if A satisfies a then return (A)
            }

            vector<int> unsatisfiedClauses;
            for (size_t i = 0; i < clauses.size(); i++) {
                if (!evaluateClause(clauses[i], assignment)) {
                    unsatisfiedClauses.push_back(i); // c := randomly chosen unsatisfied clause
                }
            }

            int clauseIndex = unsatisfiedClauses[rand() % unsatisfiedClauses.size()];
            int varToFlip = selectVariable(clauses[clauseIndex], assignment, clauses); // x := choose a variable in c using a heuristic
            assignment[varToFlip] = !assignment[varToFlip]; // flip value of x in A
        }
    }

    if (!bestAssignment.empty()) {
        cout << "Best state found with cost: " << bestCost << endl;
        return bestAssignment;
    } else {
        cout << "No solution found after maximum tries. Best cost: " << bestCost << endl;
        return {}; // return (“No model found”)
    }
}
/////////////////////////////////////////////////////////////////////////
//////////////////////////////WALKSATWITH-A//////////////////////////////
/////////////////////////////////////////////////////////////////////////

//Main function
int main() {

    srand(static_cast < unsigned int > (time(0)));

    if (NumberofClauses > (NumberofVariables * (NumberofVariables - 1) * (NumberofVariables - 2)) / 6) {
        cout << "Error: Too many clauses requested for given number of variables" << endl;
        return 1;
    }

    getValidInput();

    // Generate and solve each problem
    for (int i = 0; i < NumberofProblems; ++i) {
        cout << "\n3-SAT Problem " << i + 1 << ":\n";
        vector < vector < int >> problem = generate3SATProblem();
        display3SATProblem(problem);

        cout << "Starting walkSAT: "<< endl;
        cout << endl;
        vector < bool > solution = walkSAT(problem); // Solve the problem using WalkSAT

        if (!solution.empty()) {
            displayAssignment(solution);
        } else {
            cout << "No solution found after maximum tries." << endl;
        }

        cout << "Starting walkSATwithA: "<< endl;
        cout << endl;
        vector < bool > solution1 = walkSATwithA(problem); // Solve the problem using WalkSAT with a

        if (!solution1.empty()) {
            displayAssignment(solution1);
        } else {
            cout << "No solution found after maximum tries." << endl;
        }
    }
    return 0;
}