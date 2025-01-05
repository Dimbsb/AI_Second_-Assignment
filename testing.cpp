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
int maxTries; // Maximum attempts 
int maxFlips; // Maximum flips 
double negativeProbability; // Probability of generating negative literals
double p; // Probability for random walk 
double a; // Parameter for semi-infinite initial state creation

////////////////////////////////////////////////////////////////////////
/////////////////////////3SAT-PROBLEM-GENERATOR/////////////////////////
////////////////////////////////////////////////////////////////////////

//This function generates a random literal (positive or negative variable)
int LiteralGeneration() {
  int literal = rand() % NumberofVariables + 1; //We generate a random variable index between 1 and NumberofVariables
  if (static_cast < double > (rand()) / RAND_MAX < negativeProbability) { //Randomly decide the literal (negative-positive)
    literal = -literal; //Make literal negative with probability based on negativeProbability
  }
  return literal; // Return the generated literal
}

//This function aims into checking if a clause is correct
//In order to avoid them
bool ClauseValidation(const vector < int > & clause) {
  unordered_set < int > checked; //Here we declare a set named checked in order to track checked literals
  for (int literal: clause) {
    if (checked.count(-literal) || checked.count(literal)) { //We check for errors like (x and ¬x) or duplication (x and x)
      return false;
    }
    checked.insert(literal); // Add literal to checked set
  }
  return true; // Clause is valid
}

//In this function we convert clause into string in order to check if it is unique
string clauseToString(const vector < int > & clause) {
  vector < int > sortedClause = clause;
  sort(sortedClause.begin(), sortedClause.end());
  string encoding = "C";
  for (int literal: sortedClause) {
    encoding += " " + to_string(literal);
  }
  return encoding;
}

//In this function we practically generate a random 3-SAT problem according to the instructions of the exercise
vector < vector < int >> generate3SATProblem() {
  vector < vector < int >> clauses(NumberofClauses, vector < int > (3)); // Create a vector for clauses, each one of the clauses has 3 literals
  unordered_set < string > uniqueClauses; //Here we create a set named uniqueClauses in order to store the unique clauses

  // Counter to check if we have reached the desired number of clauses
  int clauseCounter = 0;
  while (clauseCounter < NumberofClauses) {
    vector < int > clause(3); // Generate a clause with three random literals
    for (int i = 0; i < 3; ++i) {
      clause[i] = LiteralGeneration(); // Generate each literal
    }
    // Skip invalid or duplicated clauses, check if the clause is valid
    if (!ClauseValidation(clause)) continue;
    string clauseStr = clauseToString(clause);
    if (uniqueClauses.count(clauseStr)) continue;
    clauses[clauseCounter] = clause; // Store the valid and unique clause into uniqueClauses set
    uniqueClauses.insert(clauseStr);
    clauseCounter++;
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
bool InputValidation() {

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
/////////////////////////////COMMON-FUNCTIONS////////////////////////////
/////////////////////////////////////////////////////////////////////////
//This function is used in all of three algorithms in order to compute the cost
int calculateCost(const vector < vector < int >> & clauses,
  const vector < bool > & assignment) {
  int cost = 0;
  for (const auto & clause: clauses) {
    bool clauseSatisfied = false;

    // Evaluate the clause
    for (int literal: clause) {
      int variableIndex = abs(literal) - 1; // Get variable index (0-based)
      bool variableValue = assignment[variableIndex]; // Get assignment for this variable

      // Negate value if literal is negative
      if (literal < 0) {
        variableValue = !variableValue;
      }

      if (variableValue) {
        clauseSatisfied = true; // Clause is satisfied if any literal is true
        break;
      }
    }

    if (!clauseSatisfied) {
      cost++; // Increment cost for unsatisfied clause
    }
  }
  return cost; // Return total unsatisfied clauses (cost)
}

//This function is used in all of three algorithms in order to display the result-solution
void displayAssignment(const vector < bool > & assignment) {
  cout << "Solution: ";
  for (size_t i = 0; i < assignment.size(); i++) {
    cout << "x" << (i + 1) << "=" << assignment[i] << " "; // Display the assignment of each variable
  }
  cout << endl;
}

/////////////////////////////////////////////////////////////////////////
/////////////////////////////COMMON-FUNCTIONS////////////////////////////
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
///////////////////////////////////GSAT//////////////////////////////////
/////////////////////////////////////////////////////////////////////////

// GSAT Algorithm
vector < bool > GSAT(const vector < vector < int >> & clauses, int numVariables, int maxTries, int maxFlips, int & bestCost) {
  bestCost = NumberofClauses; // Αρχικό κόστος: ο μέγιστος αριθμός μη ικανοποιημένων όρων
  vector < bool > bestAssignment;

  for (int i = 1; i <= maxTries; ++i) {
    // Step 1: Generate a random assignment
    vector < bool > assignment(numVariables);
    for (int k = 0; k < numVariables; ++k) {
      assignment[k] = rand() % 2; // Randomly assign true or false
    }

    for (int j = 1; j <= maxFlips; ++j) {
      int currentCost = calculateCost(clauses, assignment);
      if (currentCost < bestCost) {
        bestCost = currentCost;
        bestAssignment = assignment;
      }
      if (bestCost == 0) {
        return bestAssignment; // Βρέθηκε λύση
      }

      // Step 3: Find the best variable to flip
      int minCost = currentCost;
      int bestVariable = -1;

      for (int variable = 0; variable < numVariables; ++variable) {
        vector < bool > tempAssignment = assignment;
        tempAssignment[variable] = !tempAssignment[variable]; // Flip the variable
        int tempCost = calculateCost(clauses, tempAssignment);
        if (tempCost < minCost) {
          minCost = tempCost;
          bestVariable = variable;
        }
      }

      // Step 4: Flip the value of the chosen variable
      if (bestVariable != -1) {
        assignment[bestVariable] = !assignment[bestVariable];
      }
    }
  }
  return bestAssignment;
}

/////////////////////////////////////////////////////////////////////////
///////////////////////////////////GSAT//////////////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////GSAT+RW////////////////////////////////
/////////////////////////////////////////////////////////////////////////

// GSAT with Random Walk (GSAT+RW) Algorithm Implementation
vector < bool > GSATwithRW(const vector < vector < int >> & clauses, int & bestCost) {
  // Initialize best cost to worst possible value (all clauses unsatisfied)
  bestCost = NumberofClauses;
  vector < bool > bestAssignment;

  // for i := 1 to maxTries do
  for (int i = 1; i <= maxTries; ++i) {
    // A := randomly chosen assignment of the variables in a
    // Generate initial assignment based on parameter 'a'
    vector < bool > assignment(NumberofVariables);
    for (int k = 0; k < NumberofVariables; ++k) {
      assignment[k] = static_cast < double > (rand()) / RAND_MAX < a;
    }

    // for j := 1 to maxFlips do
    for (int j = 1; j <= maxFlips; ++j) {
      // Calculate current cost and update best solution if better
      int currentCost = calculateCost(clauses, assignment);
      if (currentCost < bestCost) {
        bestCost = currentCost;
        bestAssignment = assignment;
      }

      // if A satisfies a then return (A)
      if (currentCost == 0) {
        return assignment; // Solution found
      }

      // with probability p set
      if (static_cast < double > (rand()) / RAND_MAX < p) {
        // x := variable whose flip satisfies the maximum number of clauses
        int bestVariable = -1;
        int maxSatisfied = -1;

        // Try flipping each variable and count satisfied clauses
        for (int
          var = 0;
          var < NumberofVariables;
          var ++) {
          vector < bool > tempAssignment = assignment;
          tempAssignment[var] = !tempAssignment[var];
          int satisfiedCount = clauses.size() - calculateCost(clauses, tempAssignment);

          if (satisfiedCount > maxSatisfied) {
            maxSatisfied = satisfiedCount;
            bestVariable =
              var;
          }
        }

        // Flip the variable that satisfies maximum clauses
        if (bestVariable != -1) {
          assignment[bestVariable] = !assignment[bestVariable];
        }
      }
      // with probability 1-p set
      else {
        // Find unsatisfied clauses
        vector < int > unsatisfiedClauses;
        for (size_t k = 0; k < clauses.size(); k++) {
          if (calculateCost({
              clauses[k]
            }, assignment) > 0) {
            unsatisfiedClauses.push_back(k);
          }
        }

        if (!unsatisfiedClauses.empty()) {
          // x := randomly selected variable appearing in a false clause
          int randomClauseIdx = unsatisfiedClauses[rand() % unsatisfiedClauses.size()];
          const vector < int > & falseClause = clauses[randomClauseIdx];

          // Select random variable from the false clause
          int randomLiteral = falseClause[rand() % falseClause.size()];
          int randomVar = abs(randomLiteral) - 1;

          // flip value of x in A
          assignment[randomVar] = !assignment[randomVar];
        }
      }
    }
  }

  return bestAssignment; // Return best assignment found if no solution
}

/////////////////////////////////////////////////////////////////////////
/////////////////////////////////GSAT+RW////////////////////////////////
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
//Just like calculate cost but checking one clause
bool evaluateClause(const vector < int > & clause,
  const vector < bool > & assignment) {
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
int countSatisfiedClauses(const vector < vector < int >> & clauses,
  const vector < bool > & assignment) {
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
int SelectVariabletoFlip(const vector < int > & clause, vector < bool > & assignment,
  const vector < vector < int >> & clauses) {
  vector < int > changedVariables; // Variables that improve the solution
  int currentSatisfied = countSatisfiedClauses(clauses, assignment); // Count currently satisfied clauses

  for (int literal: clause) { // Find variables that improve solution when flipped
    int variable = abs(literal) - 1;
    assignment[variable] = !assignment[variable]; // Flip the variable
    int newSatisfied = countSatisfiedClauses(clauses, assignment); // Count satisfied clauses after flip
    assignment[variable] = !assignment[variable]; // Restore original assignment

    if (newSatisfied > currentSatisfied) {
      changedVariables.push_back(variable); // Add variable to improving variables if it practically improves the clauses
    }
  }

  // If improving variables exist then choose randomly from them
  if (!changedVariables.empty()) {
    return changedVariables[rand() % changedVariables.size()]; // Return variable that improves our clauses randomly
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
vector < bool > walkSAT(const vector < vector < int >> & clauses) {
  vector < bool > bestAssignment;
  int bestCost = clauses.size();

  for (int i = 1; i <= maxTries; ++i) { //for i :=1 to maxTries do

    vector < bool > assignment = generateRandomAssignment(); // Random assignment for the variables

    for (int j = 1; j <= maxFlips; ++j) { //for j:=1 to maxFlips do
      int currentCost = calculateCost(clauses, assignment);

      // If the current cost is better (lower) than the best cost, update best assignment and cost
      if (currentCost < bestCost) {
        bestCost = currentCost;
        bestAssignment = assignment;
      }

      if (currentCost == 0) {
        return assignment; // Solution found
      }

      vector < int > unsatisfiedClauses;
      for (size_t i = 0; i < clauses.size(); i++) { // Find all unsatisfied clauses
        if (calculateCost({
            clauses[i]
          }, assignment) > 0) {
          unsatisfiedClauses.push_back(i);
        }
      }

      int clauseInput = unsatisfiedClauses[rand() % unsatisfiedClauses.size()]; //  c := randomly chosen unsatisfied clause

      // Random walk with probability p
      if (static_cast < double > (rand()) / RAND_MAX < p) {
        int randomVariableInput = abs(clauses[clauseInput][rand() % 3]) - 1;
        assignment[randomVariableInput] = !assignment[randomVariableInput];
      } else {
        int variableFlip = SelectVariabletoFlip(clauses[clauseInput], assignment, clauses); // x := choose a variable in c using a heuristic
        assignment[variableFlip] = !assignment[variableFlip]; // flip value of x in A
      }
    }
  }

  cout << "Best cost found by WalkSAT: " << bestCost << endl;
  return bestAssignment; // No solution found
}

/////////////////////////////////////////////////////////////////////////
/////////////////////////////////WALKSAT/////////////////////////////////
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
//////////////////////////////WALKSATWITH-A//////////////////////////////
/////////////////////////////////////////////////////////////////////////

//In this function we generate random initial assignments with semi-infinite initial state creation
vector < bool > generateRandomAssignmentWalkWithA() {
  vector < bool > assignment(NumberofVariables); //Here we hold variable assignments
  for (int i = 0; i < NumberofVariables; i++) {
    assignment[i] = static_cast < double > (rand()) / RAND_MAX < a; // Assign true/false based on parameter 'a'
  }
  return assignment; // Return the random assignment
}

// WalkSAT algorithm implementation with (a)
vector < bool > walkSATwithA(const vector < vector < int >> & clauses) {
  vector < bool > bestAssignment;
  int bestCost = clauses.size();

  for (int i = 1; i <= maxTries; ++i) { //for i :=1 to maxTries do
    vector < bool > assignment = generateRandomAssignmentWalkWithA(); // Step 1: A := randomly chosen assignment of the variables in 'a'

    for (int j = 1; j <= maxFlips; ++j) { //for j:=1 to maxFlips do
      int currentCost = calculateCost(clauses, assignment);

      // If the current cost is better (lower) than the best cost, update best assignment and cost
      if (currentCost < bestCost) {
        bestCost = currentCost;
        bestAssignment = assignment;
      }

      if (currentCost == 0) {
        return assignment; // Solution found
      }

      vector < int > unsatisfiedClauses;
      for (size_t i = 0; i < clauses.size(); i++) { // Find all unsatisfied clauses
        if (calculateCost({
            clauses[i]
          }, assignment) > 0) {
          unsatisfiedClauses.push_back(i);
        }
      }

      int clauseInput = unsatisfiedClauses[rand() % unsatisfiedClauses.size()]; //  c := randomly chosen unsatisfied clause

      // Random walk with probability p
      if (static_cast < double > (rand()) / RAND_MAX < p) {
        int randomVariableInput = abs(clauses[clauseInput][rand() % 3]) - 1;
        assignment[randomVariableInput] = !assignment[randomVariableInput];
      } else {
        int variableFlip = SelectVariabletoFlip(clauses[clauseInput], assignment, clauses); // x := choose a variable in c using a heuristic
        assignment[variableFlip] = !assignment[variableFlip]; // flip value of x in A
      }
    }
  }

  cout << "Best cost found by WalkSATwithA: " << bestCost << endl;
  return bestAssignment; // No solution found
}

/////////////////////////////////////////////////////////////////////////
//////////////////////////////WALKSATWITH-A//////////////////////////////
/////////////////////////////////////////////////////////////////////////

//Main function
//Main function
int main() {

  srand(static_cast < unsigned int > (time(0)));

  if (NumberofClauses > (NumberofVariables * (NumberofVariables - 1) * (NumberofVariables - 2)) / 6) {
    cout << "Error: Too many clauses requested for given number of variables" << endl;
    return 1;
  }

  InputValidation();

  // Generate and solve each problem
  for (int i = 0; i < NumberofProblems; ++i) {
    cout << "\n3-SAT Problem " << i + 1 << ":\n";
    vector < vector < int >> problem = generate3SATProblem();
    display3SATProblem(problem);
    cout << endl;

    cout << "Starting walkSAT: " << endl;
    vector < bool > solution = walkSAT(problem); // Solve the problem using WalkSAT

    if (!solution.empty()) {
      displayAssignment(solution);
    } else {
      cout << "No solution found after maximum tries." << endl;
    }

    cout << endl;
    cout << "Starting walkSATwithA: " << endl;
    vector < bool > solution1 = walkSATwithA(problem); // Solve the problem using WalkSAT with a

    if (!solution1.empty()) {
      displayAssignment(solution1);
    } else {
      cout << "No solution found after maximum tries." << endl;
    }

    int bestCost;
    vector < bool > result = GSAT(problem, NumberofVariables, maxTries, maxFlips, bestCost); // Solve the problem using gsat

    if (bestCost == 0) {
      cout << "\nSatisfying assignment found:\n";
      for (size_t i = 0; i < result.size(); ++i) {
        cout << "x" << i + 1 << ": " << (result[i] ? "True" : "False") << "\n";
      }
    } else {
      cout << "\nNo satisfying assignment found.\n";
    }

    cout << "Best cost: " << bestCost << "\n";

    cout << "\nStarting GSAT+RW:" << endl;

    vector < bool > gsatrwSolution = GSATwithRW(problem, bestCost);

    if (!gsatrwSolution.empty()) {
      cout << "GSAT+RW found solution with cost: " << bestCost << endl;
      displayAssignment(gsatrwSolution);
    } else {
      cout << "GSAT+RW: No solution found after maximum tries." << endl;
    }

  }
  return 0;
}