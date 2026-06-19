%%%%%%%%%%%%%
%
% Fit networks to reproduce formula of the best one-shot separability
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

distribs = ["Cauchy", "Cube", "Exp", "Gauss", "Laplace", "Pareto"];

% Specify number of distribution. If you want to add new distribution, you
% should add distribution's name to distribs and add corresponding content
% for function theBest.m

dists = 5; 

distr = distribs(dists);

% Dimensions to train NN
dims = [5:15, 20:5:80]';
nDim = length(dims);

% For different size of networks
maxSize = 5;
% Number of NNs to select the best
nNN = 100;

dataFile = distr + "/" + distr + 'AllData.mat';
NNFileDraft = distr + "/NNs/theBestNN_%d.mat";

function res = theBestNet(dim, num)
% theBestNet creates shellow network with three layers: input layer with
% dim neurons, fully connected hidden layer with num neurons, zero biases
% and random weights, fully conected layer with dim neurons and final layer
% that normalises length of output vector to unit length.
%
% Inputs:
%   dim is dimension of input and output layers
%   num is dimension of hidden layer
%
% Output:
%   res is deap learning neural network - dlnetwork

    gr = fullyConnectedLayer(num, 'Name', 'internalNetH');
    gr.Weights = rand(num, dim); 
    gr.Bias = zeros(num, 1);
    gr.WeightL2Factor = 0;
    layers = [featureInputLayer(dim, Name="internalNetIn"), ...
        gr, ...
        leakyReluLayer(0.01, Name="LRL"), ...
        fullyConnectedLayer(dim, 'Name', 'internalNetOut'),...
        functionLayer(@(X) (X ./ vecnorm(X)), Name='Norm')];
    lgraph = layerGraph(layers);
    res = dlnetwork(lgraph);
end

% Load data
load(dataFile);

for d = 1:nDim
    dim = dims(d);

    % Do not repeat training without necesity
    NNFileName = sprintf(NNFileDraft, dim);
    if isfile(NNFileName)
        continue
    end

    % Form data to train NN
    trSet1 = trSets1(:, 1:dim); 
    trSet2 = trSets2(:, 1:dim);
    valSet1 = valSets1(:, 1:dim); 
    valSet2 = valSets2(:, 1:dim);
    bTrain = [trSet1; trSet2];
    bValid = [valSet1; valSet2];
    % Calculate required output
    bOutT = theBest(bTrain, mu, dists);
    bOutV = theBest(bValid, mu, dists);

    % Form options for NN training
    optionsB = trainingOptions("lbfgs", ...
        ExecutionEnvironment="cpu", ...
        Plots='none', ...%"training-progress", ...
        ValidationData = {bValid, bOutV}, ... 
        ValidationFrequency = 1, ...
        ValidationPatience = 6, ...
        StepTolerance = 1.e-10, ...
        MaxIterations = 10000,...
        Verbose=true, ...
        VerboseFrequency=1);

    % Create, train and test several networks of the same type to select
    % the best
    bestB = 0;
    best = 0;
    for siz = 2:maxSize
        for nn = 1:nNN
            % Create special NN for the best formula approximation
            extB = theBestNet(dim,  siz * dim);
            % Now train NN's
            [extB, infoB] = trainnet(bTrain, bOutT, extB, 'mse', optionsB);
            
            % Retest NNs
            res = assessAcc(extB, valSet1, valSet2);
            
            if res > best
                best = res;
                bestB = extB;
            end

            % For proof of life
            fprintf("Dimension %d Size %d/5 net %d/%d Current accuracy"+...
                "%.3f The best accuracy is %.3f\n",...
                dim, siz, nn, nNN, res, best);
        end
    end
    % Save all networks and current set of accuracies
    save(NNFileName, "bestB", "best");
end
