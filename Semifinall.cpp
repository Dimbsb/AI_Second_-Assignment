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
int NumberofProblems; // Number of 3-SAT problems 
int NumberofVariables; // Number of variables in each problem
int NumberofClauses; // Number of clauses in each problem
int maxTries; // Maximum tries 
int maxFlips; // Maximum flips 
double literalProbability; // Probability of generating negative literals
double p; // Probability of random walk 
double a; // Parameter for semi-infinite initial state creation

////////////////////////////////////////////////////////////////////////
/////////////////////////3SAT-PROBLEM-GENERATOR/////////////////////////
////////////////////////////////////////////////////////////////////////

//This function generates a random literal (positive or negative variable)
int LiteralGeneration() {
  int literal = rand() % NumberofVariables + 1; //We generate a literal like {1, 2, 3, 4, 5}
  if (static_cast < double > (rand()) / RAND_MAX < literalProbability) { //Randomly decide the literal (negative-positive)
    literal = -literal; // We make literal negative with probability based on literalProbability
  }
  return literal; // Return the generated literal
}

//This function aims into checking if a clause is correct
//In order to avoid them
//We insert literals to clause at generate3SATProblem and we use it there
bool ClauseValidation(const vector < int > & clause) {
  unordered_set < int > checked; //Here we declare a set named checked in order to track checked literals
  for (int literal: clause) {//With this for we check every literal that is in clause
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
  string makeclausetostring = "C";
  for (int literal: sortedClause) {
    makeclausetostring += " " + to_string(literal);
  }
  return makeclausetostring;
}

//In this function we practically generate a random 3-SAT problem according to the instructions of the exercise
vector < vector < int >> generate3SATProblem() {

  vector < vector < int >> clauses(NumberofClauses, vector < int > (3)); // two-dimensional table C*3
  unordered_set < string > uniqueClauses; //Here we create a set named uniqueClauses in order to store the unique clauses

  // Counter to check if we have reached the desired number of clauses
  int clauseCounter = 0;
  while (clauseCounter < NumberofClauses) {
    vector < int > clause(3); // Generate a clause with three random literals
    for (int i = 0; i < 3; ++i) {
      clause[i] = LiteralGeneration(); //Here we generate each literal and put it in clause table
    }
    // Skip invalid or duplicated clauses
    // We check if the clause is valid with ClauseValidation function
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
      cout << (clauses[i][j] > 0 ? "x" : "~x") << abs(clauses[i][j]);
      if (j < clauses[i].size() - 1) cout << " OR ";
    }
    cout << ")";
    if (i < clauses.size() - 1) cout << " AND ";
  }
  cout << endl;
}

//In this function we practically aim into getting valid input from user as far as the parameters are concerned
//We check for input validation at variables like (NumberofProblems, NumberofVariables, NumberofClauses, literalProbability,maxFlips, maxTries, p)
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
    cin >> literalProbability;
  } while (literalProbability < 0 || literalProbability > 1);

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
    cout << "Enter parameter a for semi-infinite initial state creation (0-1): ";
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

//This function evaluates if a clause is satisfied by the current assignment (True/False)
//Practically we use this function in both calculate cost and the Heuristic at walksat algorithms
bool evaluateClause(const vector < int > & clause,const vector < bool > & assignment) {
  for (int literal: clause) {
    int variableInput = abs(literal) - 1; //e.g (1-1)=0...(2-1)=1
    bool variableValue = assignment[variableInput]; // variableValue=(e.g assignment[0],assignment[1]...etc )
    if (literal < 0) { 
      variableValue = !variableValue; //Here we mean that no literals are true so we return false
    }

    if (variableValue) { 
      return true;
    }
  }
  return false;
}

//This function is used in all of three algorithms in order to compute the cost
int calculateCost(const vector < vector < int >> & clauses, const vector < bool > & assignment) {
  int cost = 0;
  for (const auto & clause : clauses) {
    if (!evaluateClause(clause, assignment)) { // evaluateClause 
      cost++; // Increment cost 
    }
  }
  return cost; // Return total (cost) ... False clauses
}


//This function is used in all of three algorithms in order to display the result-solution
void displayAssignment(const vector < bool > & assignment) {
  cout << "Solution: ";
  for (size_t i = 0; i < assignment.size(); i++) {
    cout << "x" << (i + 1) << "=" << assignment[i] << " "; // Display the assignment of each variable
  }
  cout << endl;
}

//In this function we generate random initial assignments
vector < bool > generateRandomAssignment() {
  vector < bool > assignment(NumberofVariables); //Here we hold variable assignments
  for (int i = 0; i < NumberofVariables; i++) {
    assignment[i] = rand() % 2; // Randomly assign true/false
  }
  return assignment; // Return the random assignment
}

//In this function we generate random initial assignments with semi-infinite initial state creation
vector < bool > generateRandomAssignmentWalkWithA() {
  vector < bool > assignment(NumberofVariables); 
  for (int i = 0; i < NumberofVariables; i++) {
    assignment[i] = static_cast < double > (rand()) / RAND_MAX < a; // Practically we made this in order to assign true/false based on parameter 'a'
  }
  return assignment; 
}

/////////////////////////////////////////////////////////////////////////
/////////////////////////////COMMON-FUNCTIONS////////////////////////////
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
///////////////////////////////////GSAT//////////////////////////////////
/////////////////////////////////////////////////////////////////////////

// GSAT Algorithm
vector < bool > GSAT(const vector < vector < int >> & clauses, int numVariables, int maxTries, int maxFlips, int & bestCost) {
  // Initialize best cost to worst possible value (all clauses unsatisfied)
  bestCost = NumberofClauses; 
  vector < bool > bestAssignment;

    // Step 1: Perform multiple tries to explore different starting points
    for (int i = 1; i <= maxTries; ++i) { 
      // Generate a random initial assignment for the variables
      vector < bool > assignment = generateRandomAssignment(); 

      // Step 2: Perform a series of flips to try to minimize the cost
      for (int j = 1; j <= maxFlips; ++j) {
        int currentCost = calculateCost(clauses, assignment);
        // Update the best assignment if the current one is better
        if (currentCost < bestCost) {
          bestCost = currentCost;
          bestAssignment = assignment;
        }
        // If a solution with no unsatisfied clauses is found, return it
        if (bestCost == 0) {
          return bestAssignment; 
        }

        // Step 3: Find the best variable to flip
        int minCost = currentCost;
        int bestVariable = -1; // Variable to track the best flip

        // Evaluate the effect of flipping each variable
        for (int variable = 0; variable < numVariables; ++variable) {
          // Create a temporary assignment with the current variable flipped
          vector < bool > tempAssignment = assignment;
          tempAssignment[variable] = !tempAssignment[variable]; // Flip the variable

          // Calculate the cost of the flipped assignment
          int tempCost = calculateCost(clauses, tempAssignment);

          // Update the best flip if the flipped assignment reduces the cost
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

//GSAT with Random Walk (GSAT+RW) Algorithm
vector <bool> GSATwithRW(const vector < vector < int >> & clauses, int & bestCost) {
  bestCost = NumberofClauses;       //initialize best cost to worst case scenario value (all clauses unsatisfied)
  vector <bool> bestAssignment;     //vector to store the best assignment found

    for (int i = 1; i <= maxTries; ++i) {                       //attempt to find solution maxTries times
    vector <bool> assignment = generateRandomAssignment();      //random assignment for the variables

    for (int j = 1; j <= maxFlips; ++j) {                       //for each try attempt maxFlips times of flip
      int currentCost = calculateCost(clauses, assignment);     //calculate current assignment's cost

      if (currentCost < bestCost) {                             //update best solution if current solution is better
        bestCost = currentCost;
        bestAssignment = assignment;                            //save the bestAssignment so far
      }

      if (currentCost == 0) {                                   //if all clauses are satisfied (cost=0), solution found
        return assignment; 
      }

      if ((static_cast<double>(rand()) / RAND_MAX) < p) {       //based on probability p, use GSAT or GSAT+RW
        //GSAT
        int bestVariable = -1;
        int maxSatisfied = -1;

        // Try flipping each variable and count satisfied clauses
        for (int variable = 0; variable < NumberofVariables; variable++) {    //flip each variable
          vector <bool> tempAssignment = assignment;                      //create vector for temporary assignment to test flip
          tempAssignment[variable] = !tempAssignment[variable];           //flip the current variable
          int satisfiedCount = clauses.size() - calculateCost(clauses, tempAssignment);     //calculate satisfied clauses after flipping the variable

          if (satisfiedCount > maxSatisfied) {                            //if the flip satisfies more clauses 
            maxSatisfied = satisfiedCount;
            bestVariable = variable;                                      //update best variable
          }
        }

        if (bestVariable != -1) {                               //flip the variable that satisfies max clauses
          assignment[bestVariable] = !assignment[bestVariable];
        }
      }
      else {                                                    //with probability 1-p
        //RW
        vector <int> unsatisfiedClauses;                        // Find unsatisfied clauses
        for (size_t k = 0; k < clauses.size(); k++) {           //check if clause is unsatisfied
          if (calculateCost({clauses[k]}, assignment) > 0) {
            unsatisfiedClauses.push_back(k);
          }
        }

        if (!unsatisfiedClauses.empty()) {                      //if there are unsatisfied clauses use RW
          int randomClauseIdx = unsatisfiedClauses[rand() % unsatisfiedClauses.size()];     //select randomly an unsatisfied clause
          const vector <int> & falseClause = clauses[randomClauseIdx];

          int randomLiteral = falseClause[rand() % falseClause.size()];                     //select random variable from the false clause
          int randomVariable = abs(randomLiteral) - 1;

          assignment[randomVariable] = !assignment[randomVariable];                         //flip the randomly selected variable
        }
      }
    }
  }

  return bestAssignment;    //return best assignment found if no solution
}

/////////////////////////////////////////////////////////////////////////
/////////////////////////////////GSAT+RW////////////////////////////////
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
/////////////////////////////WALKSAT-HEURISTIC///////////////////////////
/////////////////////////////////////////////////////////////////////////

//In this function we count the number of satisfied clauses in our problem
int countSatisfiedClauses(const vector < vector < int >> & clauses,const vector < bool > & assignment) {
  int count = 0;
  for (const auto & clause: clauses) {
    if (evaluateClause(clause, assignment)) count++; //evaluateClause
  }
  return count;
}

// Check if all clauses are satisfied
bool isSatisfied(const vector < vector < int >> & clauses, const vector < bool > & assignment) {
  return countSatisfiedClauses(clauses, assignment) == clauses.size();
}

//In this function we select variable to flip...practically we implement heuristic
int SelectVariabletoFlip(const vector < int > & clause, vector < bool > & assignment, const vector < vector < int >> & clauses) {
  vector < int > changedVariables; // Variables that improve the number of satisfied clauses
  int currentSatisfied = countSatisfiedClauses(clauses, assignment); // counts currently satisfied clauses

  for (int literal: clause) { // Find variables that improve solution when flipped
    int variable = abs(literal) - 1;
    assignment[variable] = !assignment[variable]; // Flip the variable
    int newSatisfied = countSatisfiedClauses(clauses, assignment); // Count satisfied clauses after flip
    assignment[variable] = !assignment[variable]; // Restore original assignment...like before flipping

    if (newSatisfied > currentSatisfied) {
      changedVariables.push_back(variable); // Add variable to improving variables if it practically improves the clauses
    }
  }

   if (!changedVariables.empty()) { // If changedVariables is not empty
    return changedVariables[rand() % changedVariables.size()]; // Return a variable that improves our clauses randomly
  }

  // probability p
  if (static_cast < double > (rand()) / RAND_MAX < p) {
    return abs(clause[rand() % clause.size()]) - 1; // else flips a random variable from the given clause with probability p
  }

  // Choose variable that gives us the more correct clauses
  int bestVariable = abs(clause[0]) - 1;
  int minimumIncorrectCount = NumberofClauses;

  for (int literal: clause) {
    int variable = abs(literal) - 1;
    assignment[variable] = !assignment[variable];
    int incorrectClauses = NumberofClauses - countSatisfiedClauses(clauses, assignment); // Calculate how many clauses are incorrect after this flip
    assignment[variable] = !assignment[variable]; // Restore original assignment...like before flipping

    if (incorrectClauses < minimumIncorrectCount) {
      minimumIncorrectCount = incorrectClauses;
      bestVariable = variable; // Update bestVariable
    }
  }
  return bestVariable; // Return the variable that makes correct the most clauses
}
/////////////////////////////////////////////////////////////////////////
/////////////////////////////WALKSAT-HEURISTIC///////////////////////////
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
/////////////////////////////////WALKSAT/////////////////////////////////
/////////////////////////////////////////////////////////////////////////

vector < bool > walkSAT(const vector < vector < int >> & clauses, int &bestCost) { // WalkSAT algorithm implementation
  vector < bool > bestAssignment;
  bestCost = clauses.size();

  for (int i = 1; i <= maxTries; ++i) { //for i :=1 to maxTries do

    vector < bool > assignment = generateRandomAssignment(); // Random assignment for the variables

    for (int j = 1; j <= maxFlips; ++j) { //for j:=1 to maxFlips do
      int currentCost = calculateCost(clauses, assignment); //how many not satisfied

      //cost calculation and update bestAssignment
      if (currentCost < bestCost) {
        bestCost = currentCost;
        bestAssignment = assignment;
      }

      if (currentCost == 0) {
        return assignment; // Solution found
      }

      vector < int > unsatisfiedClauses;
      for (size_t i = 0; i < clauses.size(); i++) {
        if (calculateCost({clauses[i]}, assignment) > 0) { // find unsatisfied clauses
          unsatisfiedClauses.push_back(i); 
        }   
      }

      int clauseInput = unsatisfiedClauses[rand() % unsatisfiedClauses.size()]; //  c := randomly chosen unsatisfied clause

      // Random walk with probability p
      if (static_cast < double > (rand()) / RAND_MAX < p) {
        int randomVariableInput = abs(clauses[clauseInput][rand() % 3]) - 1;
        assignment[randomVariableInput] = !assignment[randomVariableInput]; //with probability p we flip a random literal in the previously random chosen clause 
      } else { //we use heuristic
        int variableFlip = SelectVariabletoFlip(clauses[clauseInput], assignment, clauses); // x := choose a variable in c using a heuristic
        assignment[variableFlip] = !assignment[variableFlip]; // flip value of x in A
      }
    }
  }
  return bestAssignment; // No solution found
}
/////////////////////////////////////////////////////////////////////////
/////////////////////////////////WALKSAT/////////////////////////////////
/////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////
//////////////////////////////WALKSATWITH-A//////////////////////////////
/////////////////////////////////////////////////////////////////////////

vector < bool > walkSATwithA(const vector < vector < int >> & clauses, int &bestCost) { // WalkSAT with (a) algorithm implementation semi-infinite
  vector < bool > bestAssignment;
  bestCost = clauses.size();

  for (int i = 1; i <= maxTries; ++i) { //for i :=1 to maxTries do

    vector < bool > assignment = generateRandomAssignmentWalkWithA(); // Random assignment for the variables

    for (int j = 1; j <= maxFlips; ++j) { //for j:=1 to maxFlips do
      int currentCost = calculateCost(clauses, assignment); //how many not satisfied

      //cost calculation and update bestAssignment
      if (currentCost < bestCost) {
        bestCost = currentCost;
        bestAssignment = assignment;
      }

      if (currentCost == 0) {
        return assignment; // Solution found
      }

      vector < int > unsatisfiedClauses;
      for (size_t i = 0; i < clauses.size(); i++) {
        if (calculateCost({clauses[i]}, assignment) > 0) { // find unsatisfied clauses
          unsatisfiedClauses.push_back(i); 
        }   
      }

      int clauseInput = unsatisfiedClauses[rand() % unsatisfiedClauses.size()]; //  c := randomly chosen unsatisfied clause

      // Random walk with probability p
      if (static_cast < double > (rand()) / RAND_MAX < p) {
        int randomVariableInput = abs(clauses[clauseInput][rand() % 3]) - 1;
        assignment[randomVariableInput] = !assignment[randomVariableInput]; //with probability p we flip a random literal in the previously random chosen clause 
      } else { //we use heuristic
        int variableFlip = SelectVariabletoFlip(clauses[clauseInput], assignment, clauses); // x := choose a variable in c using a heuristic
        assignment[variableFlip] = !assignment[variableFlip]; // flip value of x in A
      }
    }
  }
  return bestAssignment; // No solution found
}
/////////////////////////////////////////////////////////////////////////
//////////////////////////////WALKSATWITH-A//////////////////////////////
/////////////////////////////////////////////////////////////////////////

int main() { //Main function

  srand(static_cast < unsigned int > (time(0)));

  InputValidation();

  if (NumberofClauses > (NumberofVariables * (NumberofVariables - 1) * (NumberofVariables - 2)) / 6) {
    cout << "Error: Too many clauses requested for given number of variables" << endl;
    return 1;
  }

  // Generate and solve each problem
  for (int i = 0; i < NumberofProblems; ++i) {
    cout << "________________________________________________" << "\n3-SAT Problem " << i + 1 << ":\n";
    vector < vector < int >> problem = generate3SATProblem();
    display3SATProblem(problem);

    int bestCost; 

    cout << "\nStarting GSAT:" << endl;
    vector < bool > resultGSAT = GSAT(problem, NumberofVariables, maxTries, maxFlips, bestCost); // Solve the problem using gsat
    if (!resultGSAT.empty()) {
      cout << "GSAT cost: " << bestCost << endl;
      displayAssignment(resultGSAT);
    } else {
      cout << "GSAT: No solution found after maximum tries." << endl;
    }

    cout << "\nStarting GSAT+RW:" << endl;
    vector < bool > resultGSATRW = GSATwithRW(problem, bestCost); // Solve the problem using gsat+RW
    if (!resultGSATRW.empty()) {
      cout << "GSAT+RW cost: " << bestCost << endl;
      displayAssignment(resultGSATRW);
    } else {
      cout << "GSAT+RW: No solution found after maximum tries." << endl;
    }

    cout << endl << "Starting walkSAT: " << endl;
    vector < bool > resultwalkSAT = walkSAT(problem, bestCost); // Solve the problem using WalkSAT
    if (!resultwalkSAT.empty()) {
      cout << "walkSAT cost: " << bestCost << endl;
      displayAssignment(resultwalkSAT);
    } else {
      cout << "No solution found after maximum tries. Best cost: " << bestCost << endl;
    }

    cout << endl << "Starting walkSATwithA: " << endl;
    vector < bool > resultwalkSATwa = walkSATwithA(problem, bestCost); // Solve the problem using WalkSAT with a
    if (!resultwalkSATwa.empty()) {
      cout << "walkSATwithA cost: " << bestCost << endl;
      displayAssignment(resultwalkSATwa);
    } else {
      cout << "No solution found after maximum tries. Best cost: " << bestCost << endl;
    }
  }
  return 0;
}
