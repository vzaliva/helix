/* Change this variable to your baranch name if you want build it. */
BUILD_IF_BRANCH = 'itp21'

pipeline {
    agent { 
        dockerfile {
               filename 'Dockerfile'
               label 'DOCKER_HOST' 
               args '-u root:sudo --privileged'
        }
    }

    environment {
                NJOBS = 2
                TEST_TARGET = "8.12.2"
            }

   stages {
        stage('Build') {
	    when {
		    branch "${BUILD_IF_BRANCH}"
	    }
            steps {

	        scmSkip(deleteBuild: true, skipPattern:'.*\\[skip ci\\].*')

		script {
		    env.GIT_COMMIT_MSG = sh (script: 'git log -1 --pretty=%B ${GIT_COMMIT}', returnStdout: true).trim()
		    env.GIT_AUTHOR = sh (script: 'git log -1 --pretty=%cn ${GIT_COMMIT}', returnStdout: true).trim()
		}
	            
                sh '''
                      eval $(opam config env)
                      opam config var root
                      if [ -d lib/vellvm ]; then rm -rf lib/vellvm; fi
                      git clone -b itp21 --recurse-submodules https://github.com/vellvm/vellvm.git lib/vellvm
                      git --no-pager --git-dir=lib/vellvm/.git log -1 --pretty=oneline
                      make -j ${NJOBS} -C lib/vellvm/src
                      ln -s `pwd`/lib/vellvm/src/ml/libvellvm/ ml/
                      make -j ${NJOBS}
                      make test
                   '''
            }
        }
    }
    post {
       always {
	   /* Use slackNotifier.groovy from shared library and provide current build result as parameter */
           notifySlack(currentBuild.result)
           cleanWs()
       }
   }
}

/*   Functions   */
/* ----------------------------------------------------------------------------------------------------  */

def notifySlack(String buildStatus = 'STARTED') {
    // Build status of null means success.
    buildStatus = buildStatus ?: 'SUCCESS'

    def color

    if (buildStatus == 'STARTED') {
        color = '#D4DADF'
    } else if (buildStatus == 'SUCCESS') {
        color = '#BDFFC3'
    } else if (buildStatus == 'UNSTABLE') {
        color = '#FFFE89'
    } else {
        color = '#FF9FA1'
    }

    def msg = "Build <${env.BUILD_URL}|#${env.BUILD_NUMBER}> (${getSlackRepoURL()}) of ${env.JOB_NAME} (${env.GIT_BRANCH}) by ${env.GIT_AUTHOR} ${buildStatus} in ${currentBuild.durationString.minus(' and counting')}"
	if (env.BRANCH_NAME == "${BUILD_IF_BRANCH}" ) {
	    slackSend(color: color, message: msg, channel: '#bitbucket-activity')
    }
}

def getRepoURL() {
  sh "git config --get remote.origin.url > .git/remote-url"
  return readFile(".git/remote-url").trim()
}

def getRepoSHA() {
  sh "git rev-parse HEAD > .git/current-commit"
  return readFile(".git/current-commit").trim()
}

def getSlackRepoURL() {
  repoURL = getRepoURL()
  repoURL = repoURL.take(repoURL.length()-4) + "/commit"
  repoSHA = getRepoSHA()
  
	return "<${repoURL}|${getRepoSHA().take(7)}>"
}
