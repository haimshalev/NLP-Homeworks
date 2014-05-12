#********************** NLP **********************#
# H.W 4
# Haim Shalelashvily    200832780
# Zahi Kfir             200681476
#********************** NLP **********************#

import sys, os, time, codecs, math,re
from collections import Counter


# Return the execution mod and the appropriate command arguments
def GetCommandLineArguments():
    try:
        if len(sys.argv) < 4: 
            sys.exit()

        executionMode = sys.argv[1]
        trainFilePath = sys.argv[sys.argv.index("--train") + 1]

        if (executionMode == '-v'):         # Evaluation mode
            evalOrTestFilePath = sys.argv[sys.argv.index("--eval") + 1]
        elif (executionMode == '-t'):       # Test mode 
            evalOrTestFilePath = sys.argv[sys.argv.index("--test") + 1]
        else:                               # wrong execution mode
            sys.exit()
    
    except:                                 # if one of the option parameters is missing
        sys.exit("\nWrong input. Please check your command line arguments \nTo run hmm.py in evaluation mode run: \n\t hmm.py -v --train TRAINING_FILE.txt --eval EVALUATION_FILE.txt \nTo run hmm.py in testing mode run: \n\t hmm.py -t --train TRAINING_FILE.txt --test TESTING_FILE.txt")
    
    print('\nStart Program. \n\t Execution mode: {0} \n\t trainFilePath: {1} \n\t evalOrTestFilePath: {2}\n'.format(executionMode, trainFilePath, evalOrTestFilePath))

    return executionMode,trainFilePath,evalOrTestFilePath


# Parse the training file and returns a list of sentences, each sentence is a list of (word,POS)
def ParseTrainingFile(trainFilePath):
    returnVariable = []

    trainFile = codecs.open(trainFilePath,"r","utf-8")              # Open the train file
    trainSentences = re.split(".(?=\.|\?|\!)",trainFile.read())     # Split the train file into sentences

    currentSentence = []

    # Handle the first sentence
    trainRows = trainSentences[0].split("\n")       # Split the first sentence into row (each row represent a word/token and its labels)
    for row in trainRows:                           # For each row
        columns = row.split("\t")                   # Split the row into columns (each column represent a word/token or a label)
        if len(columns) >= 4:
            currentSentence.append( (columns[1],columns[3]) )      # (columns[1] = token) , (columns[3] = POS)

    # For each sentence (except the first)
    for sentence in trainSentences[1:]:   
        trainRows = sentence.split("\n")            # Split the sentence into row (each row represent a word/token and its labels)
    
        # The first row is the punctuation at the end of the last sentence
        columns = trainRows[0].split("\t")          # Split the row into columns (each column represent a word/token or a label)
        if len(columns) >= 4:
              currentSentence.append( (columns[0],columns[2]) )    # (columns[0] = token) , (columns[2] = POS)
        
        returnVariable.append(currentSentence)      # Push current sentence
        currentSentence = []                        # Reset current sentence

        # For each row (except the first)
        for row in trainRows[1:]:
            columns = row.split("\t")               # Split the row into columns (each column represent a word/token or a label)
            if len(columns) >= 4:
              currentSentence.append( (columns[1],columns[3]) )    # (columns[1] = token) , (columns[3] = POS)
    
    returnVariable.append(currentSentence)          # push last sentence

    # replace all empty POS with 'clitic'
    for i in range( len(returnVariable) ):
        for j in range( len(returnVariable[i]) ):
            if returnVariable[i][j][1] == '':
                returnVariable[i][j] = (returnVariable[i][j][0],'clitic')

    return returnVariable 


# Replace all the tokens that appear once to uniformToken
def BindAllSingleTokens(trainData,uniformToken):
    
    # Count token appearances
    tokenDic = Counter()        
    for sentence in trainData:
        for word in sentence:
            tokenDic.update( [word[0]] )
    
    # List all the tokens with single appearance
    appearOnceList = []
    for token,val in tokenDic.items():
        if val == 1:
            appearOnceList.append(token)

    # Replace all the tokens that appear once
    for i in range( len(trainData) ):
        for j in range( len(trainData[i]) ):
            if trainData[i][j][0] in appearOnceList:
                trainData[i][j] = (uniformToken,trainData[i][j][1])

    # Update tokenDic after the replacements
    tokenDic[uniformToken] = len(appearOnceList)
    for token in appearOnceList:
        tokenDic.pop(token)

    return trainData,tokenDic


# Get Command Line Arguments
executionMode,trainFilePath,evalOrTestFilePath = GetCommandLineArguments()

StartTime = time.clock()
trainData = ParseTrainingFile(trainFilePath)
print("ParseTrainingFile() (sec):\t" ,time.clock() - StartTime)

StartTime = time.clock()
trainData,TokenDic = BindAllSingleTokens(trainData,"Kukiritza")
print("BindAllSingleTokens()(sec):\t" ,time.clock() - StartTime)

outputFile = codecs.open("OutputFile.txt", "w", "utf-8")        # for debug only !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
for sentence in trainData:
    if len(sentence) >= 1:
        for word in sentence:
            outputFile.writelines(word[0]+ " ")
        outputFile.write(os.linesep)

print("\nHW4 - Hidden Markov model\n") 

